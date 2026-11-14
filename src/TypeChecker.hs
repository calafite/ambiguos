{-# LANGUAGE OverloadedStrings #-}

module TypeChecker (
    TypeError (..),
    TypeDiagnostic (..),
    Goal (..),
    Context (..),
    DataInfo (..),
    emptyContext,
    extendContextType,
    extendContextDefinition,
    checkDataDeclaration,
    synthesize,
    check,
    checkDefinition,
    lookupContext,
    renderTypeError,
    renderTypeDiagnostic,
    renderGoals,
) where

import AST (CaseBranch (..), Expression (..), Fixity (..), Identifier (..), Visibility (..))
import Control.Monad (filterM)
import Control.Monad.State.Strict (StateT (..), evalStateT, gets, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Diagnostics (SourceSpan (..), formatSourceSnippet)
import Parser (defaultFixityEnv)
import Evaluation (areDefinitionallyEqual, evaluateWeakHeadNormalForm)
import Pretty (prettyExpression, prettyIdentifier)
import Substitution (freeVariables, freshIdentifier, substitute)

data Goal = Goal
    { goalId :: !Int
    , goalName :: !(Maybe Identifier)
    , goalExpected :: !Expression
    , goalLocals :: ![(Identifier, Expression)]
    }
    deriving (Eq, Show)

data MetaInfo = MetaInfo
    { metaInfoName :: !(Maybe Identifier)
    , metaInfoExpected :: !Expression
    , metaInfoContext :: !Context
    }
    deriving (Eq, Show)

data DataInfo = DataInfo
    { dataParams :: ![(Visibility, Identifier, Expression)]
    , dataIndices :: ![(Visibility, Identifier, Expression)]
    , dataUniverse :: !Expression
    , dataConstructors :: ![(Identifier, Expression)]
    }
    deriving (Eq, Show)

data TypeError
    = UnboundVariable Identifier
    | TypeMismatch
        { expectedType :: Expression
        , actualType :: Expression
        }
    | ExpectedFunctionType
        { actualType :: Expression
        }
    | ExpectedUniverse
        { actualType :: Expression
        }
    | CannotSynthesizeType Expression
    | CannotMatchOnNonDataType Expression
    | NonExhaustivePatternMatch Identifier [Identifier]
    | UnknownConstructor Identifier Identifier
    | ArityMismatch Identifier Int Int
    | OccursCheckFailed Int Expression
    | ScopeEscapeFailed Int Identifier Expression
    | NonStrictlyPositive Identifier Identifier
    | NonTerminatingDefinition Identifier
    | UnsolvedMetavariable Int
    deriving (Eq, Show)

data TypeDiagnostic = TypeDiagnostic
    { diagSpan  :: !(Maybe SourceSpan)
    , diagTrace :: ![Text]
    , diagError :: !TypeError
    } deriving (Eq, Show)

data Context = Context
    { contextTypes :: Map Identifier Expression
    , contextValues :: Map Identifier Expression
    , contextLocals :: [Identifier]
    , contextData :: Map Identifier DataInfo
    , contextFixities :: Map Identifier Fixity
    }
    deriving (Eq, Show)

builtinData :: Map Identifier DataInfo
builtinData =
    Map.fromList
        [
            ( Identifier "Nat"
            , DataInfo
                { dataParams = []
                , dataIndices = []
                , dataUniverse = Universe (-1)
                , dataConstructors =
                    [ (Identifier "zero", NatType)
                    , (Identifier "successor", Pi Explicit (Identifier "_") NatType NatType)
                    ]
                }
            )
        ,
            ( Identifier "Void"
            , DataInfo
                { dataParams = []
                , dataIndices = []
                , dataUniverse = Universe (-1)
                , dataConstructors = []
                }
            )
        ]

emptyContext :: Context
emptyContext =
    Context
        { contextTypes =
            Map.fromList
                [ (Identifier "zero", NatType)
                , (Identifier "successor", Pi Explicit (Identifier "_") NatType NatType)
                ]
        , contextValues =
            Map.fromList
                [ (Identifier "zero", Zero)
                , (Identifier "successor", Succ)
                ]
        , contextLocals = []
        , contextData = builtinData
        , contextFixities = defaultFixityEnv
        }

extendContextType :: Identifier -> Expression -> Context -> Context
extendContextType identifier expressionType context =
    context
        { contextTypes = Map.insert identifier expressionType (contextTypes context)
        , contextLocals = identifier : contextLocals context
        }

extendContextDefinition :: Identifier -> Expression -> Expression -> Context -> Context
extendContextDefinition identifier expressionType expressionValue context =
    context
        { contextTypes = Map.insert identifier expressionType (contextTypes context)
        , contextValues = Map.insert identifier expressionValue (contextValues context)
        }

lookupContext :: Identifier -> Context -> Either TypeError Expression
lookupContext identifier context =
    case Map.lookup identifier (contextTypes context) of
        Just expressionType -> pure expressionType
        Nothing -> Left (UnboundVariable identifier)

data ElabState = ElabState
    { nextMetaId :: !Int
    , metaSubst :: !(Map Int Expression)
    , metaRegistry :: !(Map Int MetaInfo)
    , activeSpan :: !(Maybe SourceSpan)
    , elabTrace  :: ![Text]
    }

type Elab a = StateT ElabState (Either TypeDiagnostic) a

throwError :: TypeError -> Elab a
throwError err = do
    sp <- gets activeSpan
    trace <- gets elabTrace
    lift $ Left (TypeDiagnostic sp trace err)

liftEither :: Either TypeError a -> Elab a
liftEither (Left err) = throwError err
liftEither (Right val) = pure val

localSpan :: SourceSpan -> Elab a -> Elab a
localSpan sp action = do
    prev <- gets activeSpan
    modify (\s -> s{activeSpan = Just sp})
    result <- action
    modify (\s -> s{activeSpan = prev})
    pure result

localTrace :: Text -> Elab a -> Elab a
localTrace msg action = do
    prev <- gets elabTrace
    modify (\s -> s{elabTrace = msg : prev})
    result <- action
    modify (\s -> s{elabTrace = prev})
    pure result

catchElab :: Elab a -> (TypeDiagnostic -> Elab a) -> Elab a
catchElab (StateT action) handler = StateT $ \s ->
    case action s of
        Left diag -> runStateT (handler diag) s
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
        pure
            Goal
                { goalId = mId
                , goalName = metaInfoName info
                , goalExpected = normExp
                , goalLocals = locals
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
                Nothing -> pure (MetaVar i)
        Application vis f a -> Application vis <$> zonk f <*> zonk a
        Lambda vis p ty body -> Lambda vis p <$> traverse zonk ty <*> zonk body
        Pi vis p d c -> Pi vis p <$> zonk d <*> zonk c
        Let p ty d b -> Let p <$> traverse zonk ty <*> zonk d <*> zonk b
        Case target mMotive branches ->
            Case <$> zonk target <*> traverse zonkMotive mMotive <*> traverse zonkBranch branches
          where
            zonkMotive (mv, mt) = (,) mv <$> zonk mt
            zonkBranch (CaseBranch con vars body) = CaseBranch con vars <$> zonk body
        Annotation t ty -> Annotation <$> zonk t <*> zonk ty
        Located sp e -> Located sp <$> zonk e
        other -> pure other

occursIn :: Int -> Expression -> Bool
occursIn i expr = case expr of
    MetaVar j -> i == j
    Application _ f a -> occursIn i f || occursIn i a
    Lambda _ _ ty body -> maybe False (occursIn i) ty || occursIn i body
    Pi _ _ d c -> occursIn i d || occursIn i c
    Let _ ty d b -> maybe False (occursIn i) ty || occursIn i d || occursIn i b
    Case target mMotive branches ->
        occursIn i target || any (\(CaseBranch _ _ b) -> occursIn i b) branches || case mMotive of
            Just (_, mt) -> occursIn i mt
            Nothing -> False
    Annotation t ty -> occursIn i t || occursIn i ty
    Located _ e -> occursIn i e
    _ -> False

unfoldApp :: Expression -> (Expression, [(Visibility, Expression)])
unfoldApp expression = collect expression []
  where
    collect (Application vis fn arg) args = collect (stripLocated fn) ((vis, arg) : args)
    collect headExpr args = (stripLocated headExpr, args)

stripLocated :: Expression -> Expression
stripLocated (Located _ e) = stripLocated e
stripLocated e = e

checkPatternSpine :: [(Visibility, Expression)] -> Maybe [(Visibility, Identifier)]
checkPatternSpine = traverse extractVar
  where
    extractVar (vis, Variable ident) = Just (vis, ident)
    extractVar _ = Nothing

isLinear :: [(Visibility, Identifier)] -> Bool
isLinear vars =
    let idents = map snd vars
     in Set.size (Set.fromList idents) == length idents

solvePattern :: Context -> Int -> [(Visibility, Identifier)] -> Expression -> Elab ()
solvePattern ctx mId spine rhs = do
    zonkedRhs <- zonk rhs
    if occursIn mId zonkedRhs
        then throwError (OccursCheckFailed mId zonkedRhs)
        else do
            reg <- gets metaRegistry
            let allowedVars = case Map.lookup mId reg of
                    Just info -> Map.keysSet (contextTypes (metaInfoContext info))
                    Nothing -> Map.keysSet (contextTypes ctx)
                spineVarSet = Set.fromList (map snd spine)
                validVars = Set.union allowedVars spineVarSet
                rhsFreeVars = freeVariables zonkedRhs
                escapingVars = Set.difference rhsFreeVars validVars
            case Set.lookupMin escapingVars of
                Just escaped ->
                    throwError (ScopeEscapeFailed mId escaped zonkedRhs)
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
        other -> throwError (ExpectedUniverse other)

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
            | i <= j -> pure ()
            | otherwise -> throwError (TypeMismatch (Universe j) (Universe i))
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
                            else throwError (TypeMismatch t2 t1)
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
                | i <= j -> pure ()
                | otherwise -> throwError (TypeMismatch (Universe j) (Universe i))
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
    Pi
        Explicit
        (Identifier "A")
        (Universe (-1))
        ( Pi
            Explicit
            (Identifier "_")
            (Variable (Identifier "A"))
            (Pi Explicit (Identifier "_") (Variable (Identifier "A")) (Universe (-1)))
        )
reflexivityType =
    Pi
        Explicit
        (Identifier "A")
        (Universe (-1))
        ( Pi
            Explicit
            (Identifier "x")
            (Variable (Identifier "A"))
            ( Application
                Explicit
                ( Application
                    Explicit
                    (Application Explicit Identity (Variable (Identifier "A")))
                    (Variable (Identifier "x"))
                )
                (Variable (Identifier "x"))
            )
        )
jType =
    Pi Explicit (Identifier "A") (Universe (-1))
        $ Pi Explicit (Identifier "x") (Variable (Identifier "A"))
        $ Pi Explicit (Identifier "P") motiveType
        $ Pi Explicit (Identifier "d") baseCaseType
        $ Pi Explicit (Identifier "y") (Variable (Identifier "A"))
        $ Pi Explicit (Identifier "p") proofType codomainType
  where
    motiveType =
        Pi
            Explicit
            (Identifier "y")
            (Variable (Identifier "A"))
            ( Pi
                Explicit
                (Identifier "_")
                (Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y")))
                (Universe (-1))
            )
    baseCaseType =
        Application
            Explicit
            (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "x")))
            (Application Explicit (Application Explicit Reflexivity (Variable (Identifier "A"))) (Variable (Identifier "x")))
    proofType =
        Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y"))
    codomainType =
        Application Explicit (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "y"))) (Variable (Identifier "p"))
abortType =
    Pi
        Explicit
        (Identifier "A")
        (Universe (-1))
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

checkCaseBranches ::
    Context ->
    Expression ->
    Expression ->
    Expression ->
    Maybe (Identifier, Expression) ->
    [CaseBranch] ->
    Elab [CaseBranch]
checkCaseBranches context elabTarget whnfTargetType expType mMotive branches = do
    let (headExpr, typeArgs) = unfoldApp whnfTargetType
    dataTypeName <- case headExpr of
        Variable ident -> pure ident
        NatType -> pure (Identifier "Nat")
        VoidType -> pure (Identifier "Void")
        other -> throwError (CannotMatchOnNonDataType other)
    dataInfo <- case Map.lookup dataTypeName (contextData context) of
        Just info -> pure info
        Nothing -> throwError (CannotMatchOnNonDataType headExpr)
    let numParams = length (dataParams dataInfo)
        (paramArgs, indexArgs) = splitAt numParams typeArgs
        paramArgsExprs = map snd paramArgs
        indexArgsExprs = map snd indexArgs
        expectedConstructors = map fst (dataConstructors dataInfo)
    -- Determine which expected constructors are non-absurd (can unify with
    -- target indices). Only non-absurd constructors are required for
    -- exhaustiveness; absurd branches (e.g. vnil against Vec A (succ k)) are
    -- unreachable and need not be covered.
    expectedNonAbsurd <-
        filterM
            ( \cName ->
                isConNonAbsurd
                    context
                    dataInfo
                    paramArgsExprs
                    indexArgsExprs
                    dataTypeName
                    cName
            )
            expectedConstructors
    let branchConstructors = map branchConstructor branches
        missingConstructors =
            filter (`notElem` branchConstructors) expectedNonAbsurd
    if not (null missingConstructors) && dataTypeName /= Identifier "Void"
        then throwError (NonExhaustivePatternMatch dataTypeName missingConstructors)
        else traverse
            ( checkBranch
                context
                elabTarget
                dataInfo
                paramArgsExprs
                indexArgsExprs
                dataTypeName
                whnfTargetType
                mMotive
                expType
            )
            branches

-- | Check whether a case branch's constructor indices unify with the target's
-- indices. If they don't (e.g. `vnil` against `Vec A (successor k)`), the branch
-- is absurd/unreachable and does not count for exhaustiveness.
isConNonAbsurd ::
    Context ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Identifier ->
    Elab Bool
isConNonAbsurd context dataInfo paramArgs indexArgs dataTypeName cName = do
    localConType <-
        case lookup cName (dataConstructors dataInfo) of
            Just ty -> pure ty
            Nothing -> throwError (UnknownConstructor dataTypeName cName)
    conIndexArgs <- extractConIndexArgs context localConType paramArgs dataTypeName
    case conIndexArgs of
        Just cargs -> do
            result <-
                catchElab
                    ( unifyIndexArgs context cargs indexArgs >> pure True
                    )
                    (const (pure False))
            pure result
        Nothing -> pure (False :: Bool)

-- | Extract the index arguments from a constructor's elaborated type by peeling
-- Pi binders until reaching the data type application.
extractConIndexArgs ::
    Context -> Expression -> [Expression] -> Identifier -> Elab (Maybe [Expression])
extractConIndexArgs context expr paramArgs dataTypeName = do
    let env = contextValues context
        w = evaluateWeakHeadNormalForm env expr
    case w of
        Pi _ _ _ codom -> extractConIndexArgs context codom paramArgs dataTypeName
        NatType | dataTypeName == Identifier "Nat" -> pure (Just [])
        VoidType | dataTypeName == Identifier "Void" -> pure (Just [])
        other ->
            let (headExpr, allArgs) = unfoldApp other
             in case headExpr of
                    Variable dt
                        | dt == dataTypeName ->
                            let numParams = length paramArgs
                                (_, cargs) = splitAt numParams allArgs
                             in pure (Just (map snd cargs))
                    _ -> pure Nothing

-- | Unify each constructor index arg with the corresponding target index arg.
unifyIndexArgs :: Context -> [Expression] -> [Expression] -> Elab ()
unifyIndexArgs _ [] [] = pure ()
unifyIndexArgs context (c : cs) (t : ts) = do
    unify context c t
    unifyIndexArgs context cs ts
unifyIndexArgs _ _ _ = pure ()

checkBranch ::
    Context ->
    Expression ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Expression ->
    Maybe (Identifier, Expression) ->
    Expression ->
    CaseBranch ->
    Elab CaseBranch
checkBranch context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType (CaseBranch con vars body) = do
    localConType <-
        case lookup con (dataConstructors dataInfo) of
            Just ty -> pure ty
            Nothing -> throwError (UnknownConstructor dataTypeName con)
    let paramNames = map (\(_, p, _) -> p) (dataParams dataInfo)
        conSubst = foldr (\(p, a) acc -> substitute p a acc) localConType (zip paramNames paramArgs)
    (explicitArgTypes, _) <- peelConstructorArgs context vars conSubst
    let extContext =
            foldr (\(v, ty) ctx -> extendContextType v ty ctx) context (zip vars explicitArgTypes)
        conApp =
            case dataTypeName of
                Identifier "Nat" ->
                    if con == Identifier "zero"
                        then Zero
                        else foldl (Application Explicit) Succ (map Variable vars)
                _ ->
                    foldl
                        (Application Explicit)
                        (foldl
                            (Application Implicit)
                            (Variable con)
                            indexArgs
                        )
                        (map Variable vars)
        (refContext, branchExpected) =
            case (elabTarget, mMotive) of
                (Variable targetVar, Just (mv, mtype)) ->
                    ( extendContextDefinition targetVar whnfTargetType conApp extContext
                    , substitute targetVar conApp (substitute mv conApp mtype)
                    )
                (Variable targetVar, Nothing) ->
                    ( extendContextDefinition targetVar whnfTargetType conApp extContext
                    , substitute targetVar conApp expType
                    )
                (_, Just (mv, mtype)) ->
                    (extContext, substitute mv conApp mtype)
                _ -> (extContext, expType)
    elabBody <- checkElab refContext body branchExpected
    pure (CaseBranch con vars elabBody)

peelConstructorArgs :: Context -> [Identifier] -> Expression -> Elab ([Expression], Expression)
peelConstructorArgs _ [] ty = pure ([], ty)
peelConstructorArgs ctx (v : vs) ty = do
    let env = contextValues ctx
        wTy = evaluateWeakHeadNormalForm env ty
    case wTy of
        Pi Explicit param dom codom -> do
            (rest, finalCodom) <- peelConstructorArgs ctx vs (substitute param (Variable v) codom)
            pure (dom : rest, finalCodom)
        Pi Implicit param _ codom -> do
            m <- freshMeta ctx (Universe (-1))
            peelConstructorArgs ctx (v : vs) (substitute param m codom)
        other ->
            throwError (ExpectedFunctionType other)

synthesizeElab :: Context -> Expression -> Elab (Expression, Expression)
synthesizeElab context expression = case expression of
    Located sp inner -> localSpan sp (synthesizeElab context inner)
    Variable identifier -> do
        rawType <- liftEither (lookupContext identifier context)
        instantiateLeadingImplicits context (Variable identifier) rawType
    Universe n -> pure (Universe n, Universe (if n == -1 then 0 else n + 1))
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
    Case target mMotive branches -> do
        retMeta <- freshMeta context (Universe (-1))
        elabCase <- checkElab context (Case target mMotive branches) retMeta
        zonkedRet <- zonk retMeta
        pure (elabCase, zonkedRet)
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
                throwError (ExpectedFunctionType nonFunctionType)
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
                throwError (ExpectedFunctionType nonFunctionType)
    Lambda vis parameter (Just parameterType) body -> do
        (elabParamType, paramUniverse) <- synthesizeElab context parameterType
        _ <- extractUniverseLevel context paramUniverse
        let extendedContext = extendContextType parameter elabParamType context
        (bodyExpr, bodyType) <- synthesizeElab extendedContext body
        (bodyTypeExpr, bodyUniverse) <- synthesizeElab extendedContext bodyType
        _ <- extractUniverseLevel extendedContext bodyUniverse
        pure (Lambda vis parameter (Just elabParamType) bodyExpr, Pi vis parameter elabParamType bodyTypeExpr)
    Lambda _ _ Nothing _ ->
        throwError (CannotSynthesizeType expression)

checkElab :: Context -> Expression -> Expression -> Elab Expression
checkElab context expression expType = case expression of
    Located sp inner -> localSpan sp (checkElab context inner expType)
    _ -> do
        zonkedExpected <- zonk expType
        let env = contextValues context
            whnfExpected = evaluateWeakHeadNormalForm env zonkedExpected
        case (expression, whnfExpected) of
            (Hole mName, _) -> do
                mId <- freshMetaId
                recordMeta mId mName context zonkedExpected
                pure (MetaVar mId)
            (Case target mMotive branches, _) -> do
                (elabTarget, rawTargetType) <- synthesizeElab context target
                zonkedTargetType <- zonk rawTargetType
                let whnfTargetType = evaluateWeakHeadNormalForm env zonkedTargetType
                elabBranches <- checkCaseBranches context elabTarget whnfTargetType whnfExpected mMotive branches
                pure (Case elabTarget mMotive elabBranches)
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
            (Lambda Explicit parameter maybeDeclaredType body, MetaVar i) -> do
                dom <- case maybeDeclaredType of
                    Just declType -> do
                        (elabDeclType, _) <- synthesizeElab context declType
                        zonk elabDeclType
                    Nothing -> freshMeta context (Universe (-1))
                codom <- freshMeta (extendContextType parameter dom context) (Universe (-1))
                solvePattern context i [] (Pi Explicit parameter dom codom)
                checkElab context (Lambda Explicit parameter maybeDeclaredType body) (Pi Explicit parameter dom codom)
            (Lambda Implicit parameter maybeDeclaredType body, MetaVar i) -> do
                dom <- case maybeDeclaredType of
                    Just declType -> do
                        (elabDeclType, _) <- synthesizeElab context declType
                        zonk elabDeclType
                    Nothing -> freshMeta context (Universe (-1))
                codom <- freshMeta (extendContextType parameter dom context) (Universe (-1))
                solvePattern context i [] (Pi Implicit parameter dom codom)
                checkElab context (Lambda Implicit parameter maybeDeclaredType body) (Pi Implicit parameter dom codom)
            (otherExpr, Pi Implicit binder domain codomain) -> do
                let extendedContext = extendContextType binder domain context
                elaboratedBody <- checkElab extendedContext otherExpr codomain
                pure (Lambda Implicit binder (Just domain) elaboratedBody)
            (Lambda _ _ _ _, notPiType) ->
                throwError (ExpectedFunctionType notPiType)
            (otherExpression, _) -> do
                (elabExpr, synthesizedType) <- synthesizeElab context otherExpression
                unify context synthesizedType zonkedExpected
                pure elabExpr

-- | Peel Pi binders from a data's declared universe until reaching `Universe lvl`,
-- returning the index binders and the universe level.
peelIndexTelescope :: Context -> Expression -> Elab ([(Visibility, Identifier, Expression)], Int)
peelIndexTelescope ctx expr = go expr []
  where
    go e acc = do
        let env = contextValues ctx
            w = evaluateWeakHeadNormalForm env e
        case w of
            Pi vis p ty codom -> go codom ((vis, p, ty) : acc)
            Universe lvl -> pure (reverse acc, lvl)
            other -> throwError (ExpectedUniverse other)

-- | Strict positivity check: a data type may not occur negatively (bare, as the
-- domain of an arrow) in any of its constructor types. Occurrences applied to
-- variables (parameters/indices) are permitted, since they describe the
-- structural arguments being consumed.
checkPositive :: Identifier -> Expression -> Elab ()
checkPositive dataName expr = go False expr
  where
    go inDomain e = case e of
        Pi _ _ dom codom ->
            go True dom >> go inDomain codom
        Variable ident
            | ident == dataName && inDomain ->
                throwError (NonStrictlyPositive dataName ident)
        Application _ f a ->
            case f of
                Variable ident | ident == dataName -> go inDomain a
                _ -> go inDomain f >> go inDomain a
        Lambda _ _ _ body -> go inDomain body
        Let _ _ d b -> go inDomain d >> go inDomain b
        Case t _mMotive branches ->
            go inDomain t >> mapM_ (go inDomain . branchBody) branches
        Annotation t _ -> go inDomain t
        _ -> pure ()

-- | Structural termination check: every recursive call to `name` must apply at
-- least one argument that is a structurally smaller variable (a constructor
-- subterm obtained by pattern matching on a parameter). Variables bound by the
-- function's own lambda parameters are tracked as `params`; variables bound by
-- case patterns on a parameter are tracked as `small` (strictly smaller).
checkTermination :: Identifier -> Expression -> Either TypeError ()
checkTermination name body =
    if Set.member name (freeVariables body)
        then checkCalls name Set.empty Set.empty body
        else pure ()
  where
    checkCalls :: Identifier -> Set.Set Identifier -> Set.Set Identifier -> Expression -> Either TypeError ()
    checkCalls nm params small expr = case expr of
        Lambda _ pname _ bdy ->
            checkCalls nm (Set.insert pname params) small bdy
        Case target _mMotive branches ->
            let targetVar = case target of Variable v -> Just v; _ -> Nothing
                small' = case targetVar of
                    Just v
                        | Set.member v params || Set.member v small ->
                            Set.union small (Set.fromList (concatMap branchBindings branches))
                    _ -> small
             in mapM_ (checkBranch' nm params small') branches
          where
            checkBranch' n pp ss (CaseBranch _ vs bdy) =
                checkCalls n pp (Set.union ss (Set.fromList vs)) bdy
        Application _ f arg ->
            let (h, spine) = unfoldApp expr
             in case h of
                    Variable ident | ident == nm ->
                        if any (\(_, a) -> case a of Variable v -> Set.member v small; _ -> False) spine
                            then pure ()
                            else Left (NonTerminatingDefinition nm)
                    _ -> pure ()
            >> checkCalls nm params small f
            >> checkCalls nm params small arg
        Pi _ _ dom codom ->
            checkCalls nm params small dom >> checkCalls nm params small codom
        Let _ _ d b ->
            checkCalls nm params small d >> checkCalls nm params small b
        Annotation t _ -> checkCalls nm params small t
        _ -> pure ()

checkTerminationElab :: Identifier -> Expression -> Elab ()
checkTerminationElab nm b = case checkTermination nm b of
    Left err -> throwError err
    Right () -> pure ()

checkDataDeclaration ::
    Context ->
    Identifier ->
    [(Visibility, Identifier, Expression)] ->
    Expression ->
    [(Identifier, Expression)] ->
    Either TypeDiagnostic Context
checkDataDeclaration context dataName params univ constructors =
    let traceMsg = "while checking data declaration '" <> prettyIdentifier dataName <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (elabUniv, _) <- synthesizeElab context univ
                    (indices, lvl) <- peelIndexTelescope context elabUniv
                    let allArgs = params ++ indices
                        typeConType = foldr (\(vis, p, ty) codom -> Pi vis p ty codom) (Universe lvl) allArgs
                        contextWithType = extendContextType dataName typeConType context
                        paramContext =
                            foldr
                                (\(_, p, ty) ctx -> extendContextType p ty ctx)
                                contextWithType
                                allArgs
                    (localConstructors, fullConstructors) <-
                        unzip
                            <$> traverse
                                ( \(cName, cType) ->
                                    localTrace
                                        ("while checking constructor '" <> prettyIdentifier cName <> "'")
                                        (checkCon paramContext allArgs (cName, cType))
                                )
                                constructors
                    let dataInfo = DataInfo params indices elabUniv localConstructors
                        finalContext =
                            foldr
                                addConstructor
                                ( contextWithType
                                    { contextData =
                                        Map.insert dataName dataInfo (contextData contextWithType)
                                    }
                                )
                                fullConstructors
                    pure finalContext
            )
            (ElabState 0 Map.empty Map.empty Nothing [])
  where
    checkCon pCtx allArgs (cName, cType) = do
        (elabCType, _) <- synthesizeElab pCtx cType
        _ <- checkPositive dataName elabCType
        let fullConType =
                foldr (\(_, p, ty) codom -> Pi Implicit p ty codom) elabCType allArgs
        pure ((cName, elabCType), (cName, fullConType))
    addConstructor (cName, cType) ctx =
        extendContextDefinition cName cType (Variable cName) ctx

synthesize :: Context -> Expression -> Either TypeDiagnostic (Expression, Expression, [Goal])
synthesize context rawExpr =
    evalStateT
        ( do
            (elabExpr, rawType) <- synthesizeElab context rawExpr
            zonkedType <- zonk rawType
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            pure (zonkedExpr, zonkedType, goals)
        )
        (ElabState 0 Map.empty Map.empty Nothing [])

check :: Context -> Expression -> Expression -> Either TypeDiagnostic (Expression, [Goal])
check context rawExpr expType =
    evalStateT
        ( do
            (elabExpected, _) <- synthesizeElab context expType
            zonkedExpected <- zonk elabExpected
            elabExpr <- checkElab context rawExpr zonkedExpected
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            pure (zonkedExpr, goals)
        )
        (ElabState 0 Map.empty Map.empty Nothing [])

checkDefinition ::
    Context ->
    Identifier ->
    Maybe Expression ->
    Expression ->
    Either TypeDiagnostic (Context, Expression, [Goal])
checkDefinition context name maybeDeclaredType bodyTerm =
    let traceMsg = "while checking definition '" <> prettyIdentifier name <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (zonkedBody, finalType) <-
                        case maybeDeclaredType of
                            Just declaredType -> do
                                (elabDeclType, typeUniverse) <- synthesizeElab context declaredType
                                _ <- extractUniverseLevel context typeUniverse
                                zonkedDeclType <- zonk elabDeclType
                                -- The name is in scope for its own body (so it can
                                -- refer to itself recursively), but only in
                                -- contextTypes, not contextValues, so it stays
                                -- neutral during typechecking and cannot diverge
                                -- the elaboration.
                                let recursiveContext = extendContextType name elabDeclType context
                                elabBody <- checkElab recursiveContext bodyTerm zonkedDeclType
                                zonkedBodyTerm <- zonk elabBody
                                checkTerminationElab name zonkedBodyTerm
                                zonkedFinalType <- zonk zonkedDeclType
                                pure (zonkedBodyTerm, zonkedFinalType)
                            Nothing -> do
                                (elabBody, rawType) <- synthesizeElab context bodyTerm
                                zonkedType <- zonk rawType
                                zonkedBodyTerm <- zonk elabBody
                                checkTerminationElab name zonkedBodyTerm
                                zonkedFinalType <- zonk zonkedType
                                pure (zonkedBodyTerm, zonkedFinalType)
                    goals <- collectUnsolvedGoals
                    let updatedContext = extendContextDefinition name finalType zonkedBody context
                    pure (updatedContext, finalType, goals)
            )
            (ElabState 0 Map.empty Map.empty Nothing [])

renderGoals :: [Goal] -> Text
renderGoals goals = Text.concat (map formatGoal goals)
  where
    formatGoal g =
        let nameTag = case goalName g of
                Just ident -> "?" <> prettyIdentifier ident
                Nothing -> "?" <> Text.pack (show (goalId g))
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
    CannotMatchOnNonDataType term ->
        "Cannot pattern match on non-data type: " <> prettyExpression term
    NonExhaustivePatternMatch (Identifier dName) missing ->
        "Non-exhaustive pattern match on data type '"
            <> dName
            <> "'. Missing constructor(s):\n  "
            <> Text.intercalate ", " (map prettyIdentifier missing)
    UnknownConstructor (Identifier dName) (Identifier cName) ->
        "Constructor '" <> cName <> "' does not belong to data type '" <> dName <> "'"
    NonStrictlyPositive (Identifier dName) (Identifier cName) ->
        "Non-strictly positive occurrence of '"
            <> dName
            <> "' in constructor '"
            <> cName
            <> "'"
    NonTerminatingDefinition (Identifier name) ->
        "Non-terminating definition: recursive calls to '"
            <> name
            <> "' do not apply a structurally decreasing argument"
    ArityMismatch (Identifier cName) expected actual ->
        "Constructor '"
            <> cName
            <> "' expects "
            <> Text.pack (show expected)
            <> " arguments, but found "
            <> Text.pack (show actual)
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

renderTypeDiagnostic :: Maybe FilePath -> Maybe Text -> TypeDiagnostic -> Text
renderTypeDiagnostic mFile mSource diag =
    let tracePart =
            if null (diagTrace diag)
                then ""
                else "  " <> Text.intercalate "\n  " (diagTrace diag) <> "\n"
        snippetPart = case (mSource, diagSpan diag) of
            (Just src, Just sp) -> formatSourceSnippet mFile src sp (renderTypeError (diagError diag))
            _ -> renderTypeError (diagError diag)
     in tracePart <> snippetPart
