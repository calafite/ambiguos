{-# LANGUAGE OverloadedStrings #-}

module TypeChecker (
    TypeError (..),
    Goal (..),
    Context (..),
    emptyContext,
    extendContextType,
    extendContextDefinition,
    synthesize,
    check,
    checkDefinition,
    renderTypeError,
    renderGoals,
) where

import AST (Expression (..), Identifier (..), Visibility (..))
import Control.Monad.State.Strict (StateT (..), evalStateT, gets, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Evaluation (areDefinitionallyEqual, evaluateWeakHeadNormalForm)
import Pretty (prettyExpression, prettyIdentifier)
import Substitution (freeVariables, freshIdentifier, substitute)

data Goal = Goal
    { goalId       :: !Int
    , goalName     :: !(Maybe Identifier)
    , goalExpected :: !Expression
    , goalLocals   :: ![(Identifier, Expression)]
    }
    deriving (Eq, Show)

data MetaInfo = MetaInfo
    { metaInfoName     :: !(Maybe Identifier)
    , metaInfoExpected :: !Expression
    , metaInfoContext  :: !Context
    }
    deriving (Eq, Show)

data TypeError
    = UnboundVariable Identifier
    | TypeMismatch
        { expectedType :: Expression
        , actualType   :: Expression
        }
    | ExpectedFunctionType
        { actualType :: Expression
        }
    | ExpectedUniverse
        { actualType :: Expression
        }
    | CannotSynthesizeType Expression
    | OccursCheckFailed Int Expression
    | ScopeEscapeFailed Int Identifier Expression
    | UnsolvedMetavariable Int
    deriving (Eq, Show)

data Context = Context
    { contextTypes  :: Map Identifier Expression
    , contextValues :: Map Identifier Expression
    , contextLocals :: [Identifier]
    }
    deriving (Eq, Show)

emptyContext :: Context
emptyContext =
    Context
        { contextTypes  = Map.empty
        , contextValues = Map.empty
        , contextLocals = []
        }

extendContextType :: Identifier -> Expression -> Context -> Context
extendContextType identifier expressionType context =
    context
        { contextTypes  = Map.insert identifier expressionType (contextTypes context)
        , contextLocals = identifier : contextLocals context
        }

extendContextDefinition :: Identifier -> Expression -> Expression -> Context -> Context
extendContextDefinition identifier expressionType expressionValue context =
    context
        { contextTypes  = Map.insert identifier expressionType (contextTypes context)
        , contextValues = Map.insert identifier expressionValue (contextValues context)
        }

lookupContext :: Identifier -> Context -> Either TypeError Expression
lookupContext identifier context =
    case Map.lookup identifier (contextTypes context) of
        Just expressionType -> pure expressionType
        Nothing             -> Left (UnboundVariable identifier)

data ElabState = ElabState
    { nextMetaId   :: !Int
    , metaSubst    :: !(Map Int Expression)
    , metaRegistry :: !(Map Int MetaInfo)
    }

type Elab a = StateT ElabState (Either TypeError) a

catchElab :: Elab a -> (TypeError -> Elab a) -> Elab a
catchElab (StateT action) handler = StateT $ \s ->
    case action s of
        Left err        -> runStateT (handler err) s
        Right (res, s') -> Right (res, s')

tryElab :: Elab a -> Elab a -> Elab a
tryElab primary fallback = catchElab primary (\_ -> fallback)

freshMetaId :: Elab Int
freshMetaId = do
    idx <- gets nextMetaId
    modify (\s -> s{nextMetaId = idx + 1})
    pure idx

freshMeta :: Context -> Expression -> Elab Expression
freshMeta ctx expType = do
    mId <- freshMetaId
    recordMeta mId Nothing ctx expType
    pure (MetaVar mId)

recordMeta :: Int -> Maybe Identifier -> Context -> Expression -> Elab ()
recordMeta mId mName context expType = do
    let info = MetaInfo mName expType context
    modify (\s -> s{metaRegistry = Map.insert mId info (metaRegistry s)})

collectUnsolvedGoals :: Elab [Goal]
collectUnsolvedGoals = do
    registry <- gets metaRegistry
    substMap <- gets metaSubst
    let unsolved = Map.filterWithKey (\mId _ -> Map.notMember mId substMap) registry
    traverse toGoal (Map.toList unsolved)
  where
    toGoal (mId, info) = do
        zonkedExp <- zonk (metaInfoExpected info)
        let ctx = metaInfoContext info
            env = contextValues ctx
            normExp = evaluateWeakHeadNormalForm env zonkedExp
        locals <- traverse (zonkLocal ctx) (contextLocals ctx)
        pure Goal
            { goalId       = mId
            , goalName     = metaInfoName info
            , goalExpected = normExp
            , goalLocals   = locals
            }

    zonkLocal ctx ident = do
        let rawType = Map.findWithDefault (Universe (-1)) ident (contextTypes ctx)
        zonkedType <- zonk rawType
        let normType = evaluateWeakHeadNormalForm (contextValues ctx) zonkedType
        pure (ident, normType)

zonk :: Expression -> Elab Expression
zonk expr = do
    substMap <- gets metaSubst
    case expr of
        MetaVar i ->
            case Map.lookup i substMap of
                Just resolved -> zonk resolved
                Nothing       -> pure (MetaVar i)
        Application vis f a -> Application vis <$> zonk f <*> zonk a
        Lambda vis p ty body -> Lambda vis p <$> traverse zonk ty <*> zonk body
        Pi vis p d c -> Pi vis p <$> zonk d <*> zonk c
        Let p ty d b -> Let p <$> traverse zonk ty <*> zonk d <*> zonk b
        Annotation t ty -> Annotation <$> zonk t <*> zonk ty
        other -> pure other

occursIn :: Int -> Expression -> Bool
occursIn i expr = case expr of
    MetaVar j -> i == j
    Application _ f a -> occursIn i f || occursIn i a
    Lambda _ _ ty body -> maybe False (occursIn i) ty || occursIn i body
    Pi _ _ d c -> occursIn i d || occursIn i c
    Let _ ty d b -> maybe False (occursIn i) ty || occursIn i d || occursIn i b
    Annotation t ty -> occursIn i t || occursIn i ty
    _ -> False

unfoldApp :: Expression -> (Expression, [(Visibility, Expression)])
unfoldApp expression = collect expression []
  where
    collect (Application vis fn arg) args = collect fn ((vis, arg) : args)
    collect headExpr args                 = (headExpr, args)

checkPatternSpine :: [(Visibility, Expression)] -> Maybe [(Visibility, Identifier)]
checkPatternSpine = traverse extractVar
  where
    extractVar (vis, Variable ident) = Just (vis, ident)
    extractVar _                     = Nothing

isLinear :: [(Visibility, Identifier)] -> Bool
isLinear vars =
    let idents = map snd vars
     in Set.size (Set.fromList idents) == length idents

-- | Solves a metavariable application according to Miller pattern unification
-- with strict occurs and scope checking.
solvePattern :: Context -> Int -> [(Visibility, Identifier)] -> Expression -> Elab ()
solvePattern ctx mId spine rhs = do
    zonkedRhs <- zonk rhs
    if occursIn mId zonkedRhs
        then lift $ Left (OccursCheckFailed mId zonkedRhs)
        else do
            reg <- gets metaRegistry
            let allowedVars = case Map.lookup mId reg of
                    Just info -> Map.keysSet (contextTypes (metaInfoContext info))
                    Nothing   -> Map.keysSet (contextTypes ctx)
                spineVarSet  = Set.fromList (map snd spine)
                validVars    = Set.union allowedVars spineVarSet
                rhsFreeVars  = freeVariables zonkedRhs
                escapingVars = Set.difference rhsFreeVars validVars
            case Set.lookupMin escapingVars of
                Just escaped ->
                    lift $ Left (ScopeEscapeFailed mId escaped zonkedRhs)
                Nothing -> do
                    let solution = foldr (\(vis, param) body -> Lambda vis param Nothing body) zonkedRhs spine
                    modify (\s -> s{metaSubst = Map.insert mId solution (metaSubst s)})

extractUniverseLevel :: Context -> Expression -> Elab Int
extractUniverseLevel context expr = do
    z <- zonk expr
    let env = contextValues context
        w = evaluateWeakHeadNormalForm env z
    case w of
        Universe n -> pure n
        MetaVar i -> do
            solvePattern context i [] (Universe (-1))
            pure (-1)
        other -> lift $ Left (ExpectedUniverse other)

unify :: Context -> Expression -> Expression -> Elab ()
unify ctx e1 e2 = do
    z1 <- zonk e1
    z2 <- zonk e2
    let (h1, sp1) = unfoldApp z1
        (h2, sp2) = unfoldApp z2
    case (h1, sp1, h2, sp2) of
        (MetaVar i, [], MetaVar j, [])
            | i == j -> pure ()
            | otherwise -> do
                reg <- gets metaRegistry
                case (Map.lookup i reg, Map.lookup j reg) of
                    (Just infoI, Just infoJ) ->
                        let varsI = Map.keysSet (contextTypes (metaInfoContext infoI))
                            varsJ = Map.keysSet (contextTypes (metaInfoContext infoJ))
                         in if Set.isSubsetOf varsI varsJ
                                then solvePattern ctx j [] (MetaVar i)
                                else solvePattern ctx i [] (MetaVar j)
                    _ -> solvePattern ctx i [] (MetaVar j)
        (MetaVar i, _, MetaVar j, _)
            | i == j && sp1 == sp2 -> pure ()
        (MetaVar i, _, _, _)
            | Just spineVars <- checkPatternSpine sp1
            , isLinear spineVars ->
                tryElab (solvePattern ctx i spineVars z2) (unfoldAndRetry z1 z2)
        (_, _, MetaVar j, _)
            | Just spineVars <- checkPatternSpine sp2
            , isLinear spineVars ->
                tryElab (solvePattern ctx j spineVars z1) (unfoldAndRetry z1 z2)
        (Universe i, [], Universe j, [])
            | i == -1 || j == -1 -> pure ()
            | i <= j -> pure ()
            | otherwise -> lift $ Left (TypeMismatch (Universe j) (Universe i))
        _ -> case (z1, z2) of
            (Application v1 f1 a1, Application v2 f2 a2)
                | v1 == v2 ->
                    tryElab
                        ( do
                            unify ctx f1 f2
                            unify ctx a1 a2
                        )
                        (unfoldAndRetry z1 z2)
            (Pi v1 p1 d1 c1, Pi v2 p2 d2 c2)
                | v1 == v2 ->
                    tryElab
                        ( do
                            unify ctx d1 d2
                            if p1 == p2
                                then unify (extendContextType p1 d1 ctx) c1 c2
                                else do
                                    let fresh = freshIdentifier p1 (Set.union (freeVariables c1) (freeVariables c2))
                                        extCtx = extendContextType fresh d1 ctx
                                    unify extCtx (substitute p1 (Variable fresh) c1) (substitute p2 (Variable fresh) c2)
                        )
                        (unfoldAndRetry z1 z2)
            (Identity, Identity) -> pure ()
            (Reflexivity, Reflexivity) -> pure ()
            (J, J) -> pure ()
            (VoidType, VoidType) -> pure ()
            (Abort, Abort) -> pure ()
            (NatType, NatType) -> pure ()
            (Zero, Zero) -> pure ()
            (Succ, Succ) -> pure ()
            (NatRec, NatRec) -> pure ()
            (Variable x, Variable y) | x == y -> pure ()
            _ -> unfoldAndRetry z1 z2
  where
    unfoldAndRetry :: Expression -> Expression -> Elab ()
    unfoldAndRetry t1 t2 = do
        let env = contextValues ctx
            w1 = evaluateWeakHeadNormalForm env t1
            w2 = evaluateWeakHeadNormalForm env t2
            (wh1, wsp1) = unfoldApp w1
            (wh2, wsp2) = unfoldApp w2
            fallbackDefEq =
                if w1 /= t1 || w2 /= t2
                    then unify ctx w1 w2
                    else
                        if areDefinitionallyEqual env w1 w2
                            then pure ()
                            else lift $ Left (TypeMismatch t2 t1)
        case (wh1, wsp1, wh2, wsp2) of
            (MetaVar i, _, _, _)
                | Just spineVars <- checkPatternSpine wsp1
                , isLinear spineVars ->
                    tryElab (solvePattern ctx i spineVars w2) fallbackDefEq
            (_, _, MetaVar j, _)
                | Just spineVars <- checkPatternSpine wsp2
                , isLinear spineVars ->
                    tryElab (solvePattern ctx j spineVars w1) fallbackDefEq
            (Universe i, [], Universe j, [])
                | i == -1 || j == -1 -> pure ()
                | i <= j -> pure ()
                | otherwise -> lift $ Left (TypeMismatch (Universe j) (Universe i))
            _ -> fallbackDefEq

instantiateLeadingImplicits :: Context -> Expression -> Expression -> Elab (Expression, Expression)
instantiateLeadingImplicits context expr exprType = do
    zonkedType <- zonk exprType
    let env = contextValues context
        whnfType = evaluateWeakHeadNormalForm env zonkedType
    case whnfType of
        Pi Implicit param domain codomain -> do
            meta <- freshMeta context domain
            let newExpr = Application Implicit expr meta
                newType = substitute param meta codomain
            instantiateLeadingImplicits context newExpr newType
        _ ->
            pure (expr, zonkedType)

identityType, reflexivityType, jType, abortType, succType, natRecType :: Expression
identityType =
    Pi Explicit (Identifier "A") (Universe (-1))
        (Pi Explicit (Identifier "_") (Variable (Identifier "A"))
            (Pi Explicit (Identifier "_") (Variable (Identifier "A")) (Universe (-1))))
reflexivityType =
    Pi Explicit (Identifier "A") (Universe (-1))
        (Pi Explicit (Identifier "x") (Variable (Identifier "A"))
            (Application Explicit
                (Application Explicit
                    (Application Explicit Identity (Variable (Identifier "A")))
                    (Variable (Identifier "x")))
                (Variable (Identifier "x"))))
jType =
    Pi Explicit (Identifier "A") (Universe (-1))
        $ Pi Explicit (Identifier "x") (Variable (Identifier "A"))
        $ Pi Explicit (Identifier "P") motiveType
        $ Pi Explicit (Identifier "d") baseCaseType
        $ Pi Explicit (Identifier "y") (Variable (Identifier "A"))
        $ Pi Explicit (Identifier "p") proofType codomainType
  where
    motiveType =
        Pi Explicit (Identifier "y") (Variable (Identifier "A"))
            (Pi Explicit (Identifier "_")
                (Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y")))
                (Universe (-1)))
    baseCaseType =
        Application Explicit
            (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "x")))
            (Application Explicit (Application Explicit Reflexivity (Variable (Identifier "A"))) (Variable (Identifier "x")))
    proofType =
        Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y"))
    codomainType =
        Application Explicit (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "y"))) (Variable (Identifier "p"))
abortType =
    Pi Explicit (Identifier "A") (Universe (-1))
        (Pi Explicit (Identifier "_") VoidType (Variable (Identifier "A")))
succType =
    Pi Explicit (Identifier "_") NatType NatType
natRecType =
    Pi Explicit (Identifier "P") pType
        $ Pi Explicit (Identifier "z") zType
        $ Pi Explicit (Identifier "s") sType
        $ Pi Explicit (Identifier "n") NatType codomainType
  where
    pType = Pi Explicit (Identifier "_") NatType (Universe (-1))
    zType = Application Explicit (Variable (Identifier "P")) Zero
    nVar = Variable (Identifier "n")
    pn = Application Explicit (Variable (Identifier "P")) nVar
    psuccn = Application Explicit (Variable (Identifier "P")) (Application Explicit Succ nVar)
    sType = Pi Explicit (Identifier "n") NatType (Pi Explicit (Identifier "_") pn psuccn)
    codomainType = Application Explicit (Variable (Identifier "P")) nVar

synthesizeElab :: Context -> Expression -> Elab (Expression, Expression)
synthesizeElab context expression = case expression of
    Variable identifier -> do
        rawType <- lift (lookupContext identifier context)
        instantiateLeadingImplicits context (Variable identifier) rawType
    Universe n -> pure (Universe n, Universe (if n == -1 then -1 else n + 1))
    Identity -> pure (Identity, identityType)
    Reflexivity -> pure (Reflexivity, reflexivityType)
    J -> pure (J, jType)
    VoidType -> pure (VoidType, Universe (-1))
    Abort -> pure (Abort, abortType)
    NatType -> pure (NatType, Universe (-1))
    Zero -> pure (Zero, NatType)
    Succ -> pure (Succ, succType)
    NatRec -> pure (NatRec, natRecType)
    MetaVar i -> do
        substMap <- gets metaSubst
        case Map.lookup i substMap of
            Just term -> synthesizeElab context term
            Nothing -> do
                tMeta <- freshMeta context (Universe (-1))
                pure (MetaVar i, tMeta)
    Hole mName -> do
        tMeta <- freshMeta context (Universe (-1))
        mId <- freshMetaId
        recordMeta mId mName context tMeta
        pure (MetaVar mId, tMeta)
    Annotation term annotationType -> do
        (elabAnnType, annTypeUniverse) <- synthesizeElab context annotationType
        _ <- extractUniverseLevel context annTypeUniverse
        _ <- checkElab context term elabAnnType
        pure (term, elabAnnType)
    Let param maybeDeclaredType defExpr body -> do
        (elabDef, defType) <- case maybeDeclaredType of
            Just declaredType -> do
                (elabDeclType, typeUniverse) <- synthesizeElab context declaredType
                _ <- extractUniverseLevel context typeUniverse
                zonkedDeclType <- zonk elabDeclType
                elabVal <- checkElab context defExpr zonkedDeclType
                pure (elabVal, zonkedDeclType)
            Nothing -> do
                (elabVal, rawType) <- synthesizeElab context defExpr
                zonkedType <- zonk rawType
                pure (elabVal, zonkedType)
        zonkedDef <- zonk elabDef
        zonkedDefType <- zonk defType
        let extContext = extendContextDefinition param zonkedDefType zonkedDef context
            extContextWithLocal = extContext{contextLocals = param : contextLocals context}
        (elabBody, bodyType) <- synthesizeElab extContextWithLocal body
        zonkedBody <- zonk elabBody
        zonkedBodyType <- zonk bodyType
        let finalType = substitute param zonkedDef zonkedBodyType
        pure (Let param (Just zonkedDefType) zonkedDef zonkedBody, finalType)
    Pi vis parameter domain codomain -> do
        (elabDomain, domainUniverse) <- synthesizeElab context domain
        levelI <- extractUniverseLevel context domainUniverse
        let extendedContext = extendContextType parameter elabDomain context
        (elabCodomain, codomainUniverse) <- synthesizeElab extendedContext codomain
        levelJ <- extractUniverseLevel extendedContext codomainUniverse
        let maxLevel = if levelI == -1 || levelJ == -1 then -1 else max levelI levelJ
        pure (Pi vis parameter elabDomain elabCodomain, Universe maxLevel)
    Application Explicit function argument -> do
        (fnExpr, functionType) <- synthesizeElab context function
        (instantiatedFn, fnType) <- instantiateLeadingImplicits context fnExpr functionType
        zonkedType <- zonk fnType
        let env = contextValues context
        case evaluateWeakHeadNormalForm env zonkedType of
            Pi Explicit parameter domain codomain -> do
                elabArg <- checkElab context argument domain
                zonkedArg <- zonk elabArg
                pure (Application Explicit instantiatedFn zonkedArg, substitute parameter zonkedArg codomain)
            MetaVar i -> do
                paramDomain <- freshMeta context (Universe (-1))
                codomainMeta <- freshMeta context (Universe (-1))
                let assumedPi = Pi Explicit (Identifier "_") paramDomain codomainMeta
                solvePattern context i [] assumedPi
                elabArg <- checkElab context argument paramDomain
                zonkedArg <- zonk elabArg
                pure (Application Explicit instantiatedFn zonkedArg, substitute (Identifier "_") zonkedArg codomainMeta)
            nonFunctionType ->
                lift $ Left (ExpectedFunctionType nonFunctionType)
    Application Implicit function argument -> do
        (fnExpr, functionType) <- synthesizeElab context function
        zonkedType <- zonk functionType
        let env = contextValues context
        case evaluateWeakHeadNormalForm env zonkedType of
            Pi Implicit parameter domain codomain -> do
                elabArg <- checkElab context argument domain
                zonkedArg <- zonk elabArg
                pure (Application Implicit fnExpr zonkedArg, substitute parameter zonkedArg codomain)
            nonFunctionType ->
                lift $ Left (ExpectedFunctionType nonFunctionType)
    Lambda vis parameter (Just parameterType) body -> do
        (elabParamType, paramUniverse) <- synthesizeElab context parameterType
        _ <- extractUniverseLevel context paramUniverse
        let extendedContext = extendContextType parameter elabParamType context
        (bodyExpr, bodyType) <- synthesizeElab extendedContext body
        (bodyTypeExpr, bodyUniverse) <- synthesizeElab extendedContext bodyType
        _ <- extractUniverseLevel extendedContext bodyUniverse
        pure (Lambda vis parameter (Just elabParamType) bodyExpr, Pi vis parameter elabParamType bodyTypeExpr)
    Lambda _ _ Nothing _ ->
        lift $ Left (CannotSynthesizeType expression)

checkElab :: Context -> Expression -> Expression -> Elab Expression
checkElab context expression expectedType = do
    zonkedExpected <- zonk expectedType
    let env = contextValues context
        whnfExpected = evaluateWeakHeadNormalForm env zonkedExpected
    case (expression, whnfExpected) of
        (Hole mName, _) -> do
            mId <- freshMetaId
            recordMeta mId mName context zonkedExpected
            pure (MetaVar mId)
        (Let param maybeDeclaredType defExpr body, _) -> do
            (elabDef, defType) <- case maybeDeclaredType of
                Just declaredType -> do
                    (elabDeclType, typeUniverse) <- synthesizeElab context declaredType
                    _ <- extractUniverseLevel context typeUniverse
                    zonkedDeclType <- zonk elabDeclType
                    elabVal <- checkElab context defExpr zonkedDeclType
                    pure (elabVal, zonkedDeclType)
                Nothing -> do
                    (elabVal, rawType) <- synthesizeElab context defExpr
                    zonkedType <- zonk rawType
                    pure (elabVal, zonkedType)
            zonkedDef <- zonk elabDef
            zonkedDefType <- zonk defType
            let extContext = extendContextDefinition param zonkedDefType zonkedDef context
                extContextWithLocal = extContext{contextLocals = param : contextLocals context}
            elabBody <- checkElab extContextWithLocal body whnfExpected
            zonkedBody <- zonk elabBody
            pure (Let param (Just zonkedDefType) zonkedDef zonkedBody)
        (Lambda Explicit parameter maybeDeclaredType body, Pi Explicit binder domain codomain) -> do
            case maybeDeclaredType of
                Just declaredType -> do
                    (elabDeclType, declUniverse) <- synthesizeElab context declaredType
                    _ <- extractUniverseLevel context declUniverse
                    unify context elabDeclType domain
                Nothing -> pure ()
            let targetParameter = parameter
                substitutedCodomain = substitute binder (Variable targetParameter) codomain
                extendedContext = extendContextType targetParameter domain context
            elaboratedBody <- checkElab extendedContext body substitutedCodomain
            pure (Lambda Explicit targetParameter (Just domain) elaboratedBody)
        (Lambda Implicit parameter maybeDeclaredType body, Pi Implicit binder domain codomain) -> do
            case maybeDeclaredType of
                Just declaredType -> do
                    (elabDeclType, declUniverse) <- synthesizeElab context declaredType
                    _ <- extractUniverseLevel context declUniverse
                    unify context elabDeclType domain
                Nothing -> pure ()
            let targetParameter = parameter
                substitutedCodomain = substitute binder (Variable targetParameter) codomain
                extendedContext = extendContextType targetParameter domain context
            elaboratedBody <- checkElab extendedContext body substitutedCodomain
            pure (Lambda Implicit targetParameter (Just domain) elaboratedBody)
        (otherExpr, Pi Implicit binder domain codomain) -> do
            let extendedContext = extendContextType binder domain context
            elaboratedBody <- checkElab extendedContext otherExpr codomain
            pure (Lambda Implicit binder (Just domain) elaboratedBody)
        (Lambda _ _ _ _, notPiType) ->
            lift $ Left (ExpectedFunctionType notPiType)
        (otherExpression, _) -> do
            (elabExpr, synthesizedType) <- synthesizeElab context otherExpression
            unify context synthesizedType zonkedExpected
            pure elabExpr

synthesize :: Context -> Expression -> Either TypeError (Expression, Expression, [Goal])
synthesize context rawExpr =
    evalStateT
        ( do
            (elabExpr, rawType) <- synthesizeElab context rawExpr
            zonkedType <- zonk rawType
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            pure (zonkedExpr, zonkedType, goals)
        )
        (ElabState 0 Map.empty Map.empty)

check :: Context -> Expression -> Expression -> Either TypeError (Expression, [Goal])
check context rawExpr expectedType =
    evalStateT
        ( do
            (elabExpected, _) <- synthesizeElab context expectedType
            zonkedExpected <- zonk elabExpected
            elabExpr <- checkElab context rawExpr zonkedExpected
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            pure (zonkedExpr, goals)
        )
        (ElabState 0 Map.empty Map.empty)

checkDefinition ::
    Context ->
    Identifier ->
    Maybe Expression ->
    Expression ->
    Either TypeError (Context, Expression, [Goal])
checkDefinition context name maybeDeclaredType bodyTerm =
    evalStateT
        ( do
            (zonkedBody, finalType) <- case maybeDeclaredType of
                Just declaredType -> do
                    (elabDeclType, typeUniverse) <- synthesizeElab context declaredType
                    _ <- extractUniverseLevel context typeUniverse
                    zonkedDeclType <- zonk elabDeclType
                    elabBody <- checkElab context bodyTerm zonkedDeclType
                    zonkedBodyTerm <- zonk elabBody
                    zonkedFinalType <- zonk zonkedDeclType
                    pure (zonkedBodyTerm, zonkedFinalType)
                Nothing -> do
                    (elabBody, rawType) <- synthesizeElab context bodyTerm
                    zonkedType <- zonk rawType
                    zonkedBodyTerm <- zonk elabBody
                    zonkedFinalType <- zonk zonkedType
                    pure (zonkedBodyTerm, zonkedFinalType)
            goals <- collectUnsolvedGoals
            let updatedContext = extendContextDefinition name finalType zonkedBody context
            pure (updatedContext, finalType, goals)
        )
        (ElabState 0 Map.empty Map.empty)

renderGoals :: [Goal] -> Text
renderGoals goals = Text.concat (map formatGoal goals)
  where
    formatGoal g =
        let nameTag = case goalName g of
                Just ident -> "?" <> prettyIdentifier ident
                Nothing    -> "?" <> Text.pack (show (goalId g))
            header = "  \ESC[1;36m[" <> nameTag <> "]\ESC[0m\n"
            target = "    \ESC[1mExpected:\ESC[0m " <> prettyExpression (goalExpected g) <> "\n"
            locals =
                if null (goalLocals g)
                    then ""
                    else
                        "    \ESC[1mContext:\ESC[0m\n"
                            <> Text.concat
                                [ "      " <> prettyIdentifier v <> " : " <> prettyExpression t <> "\n"
                                | (v, t) <- reverse (goalLocals g)
                                ]
         in header <> target <> locals

renderTypeError :: TypeError -> Text
renderTypeError typeError = case typeError of
    UnboundVariable (Identifier name) ->
        "Unbound variable: '" <> name <> "'"
    TypeMismatch expected actual ->
        "Type mismatch:\n  Expected: "
            <> prettyExpression expected
            <> "\n  Actual:   "
            <> prettyExpression actual
    ExpectedFunctionType actual ->
        "Expected a function (Pi) type, but encountered:\n  "
            <> prettyExpression actual
    ExpectedUniverse actual ->
        "Expected a Type universe, but encountered:\n  "
            <> prettyExpression actual
    CannotSynthesizeType term ->
        "Cannot synthesize type for unannotated expression:\n  "
            <> prettyExpression term
            <> "\nProvide an explicit type annotation: (term : Type)"
    OccursCheckFailed i term ->
        "Occurs check failed: ?" <> Text.pack (show i) <> " occurs in " <> prettyExpression term
    ScopeEscapeFailed i (Identifier var) term ->
        "Scope escape error: Variable '"
            <> var
            <> "' cannot appear in the solution for ?"
            <> Text.pack (show i)
            <> " := "
            <> prettyExpression term
            <> " because it was bound outside the metavariable's scope."
    UnsolvedMetavariable i ->
        "Unsolved metavariable: ?" <> Text.pack (show i)
