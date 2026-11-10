{-# LANGUAGE OverloadedStrings #-}

module TypeChecker (
    TypeError (..),
    Context (..),
    emptyContext,
    extendContextType,
    extendContextDefinition,
    synthesize,
    check,
    checkDefinition,
    renderTypeError,
) where

import AST (Expression (..), Identifier (..), Visibility (..))
import Control.Monad.State.Strict (StateT (..), evalStateT, gets, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Evaluation (areDefinitionallyEqual, evaluateWeakHeadNormalForm, normalize)
import Pretty (prettyExpression)
import Substitution (freeVariables, freshIdentifier, substitute)

data TypeError
    = UnboundVariable Identifier
    | TypeMismatch
        { expectedType :: Expression
        , actualType :: Expression
        }
    | ExpectedFunctionType
        { actualType :: Expression
        }
    | CannotSynthesizeType Expression
    | OccursCheckFailed Int Expression
    | UnsolvedMetavariable Int
    deriving (Eq, Show)

data Context = Context
    { contextTypes :: Map Identifier Expression
    , contextValues :: Map Identifier Expression
    }
    deriving (Eq, Show)

emptyContext :: Context
emptyContext =
    Context
        { contextTypes = Map.empty
        , contextValues = Map.empty
        }

extendContextType :: Identifier -> Expression -> Context -> Context
extendContextType identifier expressionType context =
    context{contextTypes = Map.insert identifier expressionType (contextTypes context)}

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
        Nothing             -> Left (UnboundVariable identifier)

data ElabState = ElabState
    { nextMetaId :: !Int
    , metaSubst  :: !(Map Int Expression)
    }

type Elab a = StateT ElabState (Either TypeError) a

catchElab :: Elab a -> (TypeError -> Elab a) -> Elab a
catchElab (StateT action) handler = StateT $ \s ->
    case action s of
        Left err        -> runStateT (handler err) s
        Right (res, s') -> Right (res, s')

tryElab :: Elab a -> Elab a -> Elab a
tryElab primary fallback = catchElab primary (\_ -> fallback)

freshMetaVar :: Elab Expression
freshMetaVar = do
    idx <- gets nextMetaId
    modify (\s -> s { nextMetaId = idx + 1 })
    pure (MetaVar idx)

instantiateHoles :: Expression -> Elab Expression
instantiateHoles expr = case expr of
    Hole _ -> freshMetaVar
    Application vis f a -> Application vis <$> instantiateHoles f <*> instantiateHoles a
    Lambda vis p ty body -> Lambda vis p <$> traverse instantiateHoles ty <*> instantiateHoles body
    Pi vis p d c -> Pi vis p <$> instantiateHoles d <*> instantiateHoles c
    Annotation t ty -> Annotation <$> instantiateHoles t <*> instantiateHoles ty
    other -> pure other

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
        Annotation t ty -> Annotation <$> zonk t <*> zonk ty
        other -> pure other

occursIn :: Int -> Expression -> Bool
occursIn i expr = case expr of
    MetaVar j -> i == j
    Application _ f a -> occursIn i f || occursIn i a
    Lambda _ _ ty body -> maybe False (occursIn i) ty || occursIn i body
    Pi _ _ d c -> occursIn i d || occursIn i c
    Annotation t ty -> occursIn i t || occursIn i ty
    _ -> False

unify :: Map Identifier Expression -> Expression -> Expression -> Elab ()
unify env e1 e2 = do
    z1 <- zonk e1
    z2 <- zonk e2
    case (z1, z2) of
        (MetaVar i, MetaVar j) | i == j -> pure ()
        (MetaVar i, term) -> bindMeta i term
        (term, MetaVar j) -> bindMeta j term

        (Application v1 f1 a1, Application v2 f2 a2) | v1 == v2 ->
            tryElab
                (do unify env f1 f2
                    unify env a1 a2)
                (unfoldAndRetry z1 z2)

        (Pi v1 p1 d1 c1, Pi v2 p2 d2 c2) | v1 == v2 ->
            tryElab
                (do unify env d1 d2
                    if p1 == p2
                        then unify env c1 c2
                        else do
                            let fresh = freshIdentifier p1 (Set.union (freeVariables c1) (freeVariables c2))
                            unify env (substitute p1 (Variable fresh) c1) (substitute p2 (Variable fresh) c2))
                (unfoldAndRetry z1 z2)

        (Universe, Universe) -> pure ()
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
    unfoldAndRetry t1 t2 = do
        let w1 = evaluateWeakHeadNormalForm env t1
            w2 = evaluateWeakHeadNormalForm env t2
        case (w1, w2) of
            (MetaVar i, term) -> bindMeta i term
            (term, MetaVar j) -> bindMeta j term
            _ ->
                if w1 /= t1 || w2 /= t2
                    then unify env w1 w2
                    else if areDefinitionallyEqual env w1 w2
                        then pure ()
                        else lift $ Left (TypeMismatch t2 t1)

    bindMeta :: Int -> Expression -> Elab ()
    bindMeta i term
        | occursIn i term = lift $ Left (OccursCheckFailed i term)
        | otherwise = modify (\s -> s { metaSubst = Map.insert i term (metaSubst s) })

-- | Automatically instantiates leading Implicit Pi parameters: {A : Type} -> ... with MetaVars
instantiateLeadingImplicits :: Context -> Expression -> Expression -> Elab (Expression, Expression)
instantiateLeadingImplicits context expr exprType = do
    zonkedType <- zonk exprType
    let env = contextValues context
        whnfType = evaluateWeakHeadNormalForm env zonkedType
    case whnfType of
        Pi Implicit param domain codomain -> do
            meta <- freshMetaVar
            let newExpr = Application Implicit expr meta
                newType = substitute param meta codomain
            instantiateLeadingImplicits context newExpr newType
        _ ->
            pure (expr, zonkedType)

identityType, reflexivityType, jType, abortType, succType, natRecType :: Expression
identityType =
    Pi Explicit (Identifier "A") Universe
        (Pi Explicit (Identifier "_") (Variable (Identifier "A"))
            (Pi Explicit (Identifier "_") (Variable (Identifier "A")) Universe))

reflexivityType =
    Pi Explicit (Identifier "A") Universe
        (Pi Explicit (Identifier "x") (Variable (Identifier "A"))
            (Application Explicit
                (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x")))
                (Variable (Identifier "x"))))

jType =
    Pi Explicit (Identifier "A") Universe
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
                Universe)
    baseCaseType =
        Application Explicit (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "x")))
            (Application Explicit (Application Explicit Reflexivity (Variable (Identifier "A"))) (Variable (Identifier "x")))
    proofType =
        Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y"))
    codomainType =
        Application Explicit (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "y"))) (Variable (Identifier "p"))

abortType =
    Pi Explicit (Identifier "A") Universe
        (Pi Explicit (Identifier "_") VoidType (Variable (Identifier "A")))

succType =
    Pi Explicit (Identifier "_") NatType NatType

natRecType =
    Pi Explicit (Identifier "P") pType
        $ Pi Explicit (Identifier "z") zType
        $ Pi Explicit (Identifier "s") sType
        $ Pi Explicit (Identifier "n") NatType codomainType
  where
    pType = Pi Explicit (Identifier "_") NatType Universe
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

    Universe    -> pure (Universe, Universe)
    Identity    -> pure (Identity, identityType)
    Reflexivity -> pure (Reflexivity, reflexivityType)
    J           -> pure (J, jType)
    VoidType    -> pure (VoidType, Universe)
    Abort       -> pure (Abort, abortType)
    NatType     -> pure (NatType, Universe)
    Zero        -> pure (Zero, NatType)
    Succ        -> pure (Succ, succType)
    NatRec      -> pure (NatRec, natRecType)

    MetaVar i   -> do
        substMap <- gets metaSubst
        case Map.lookup i substMap of
            Just term -> synthesizeElab context term
            Nothing   -> do
                tMeta <- freshMetaVar
                pure (MetaVar i, tMeta)

    Hole _ -> do
        m <- freshMetaVar
        tm <- freshMetaVar
        pure (m, tm)

    Annotation term annotationType -> do
        _ <- checkElab context annotationType Universe
        _ <- checkElab context term annotationType
        pure (term, annotationType)

    Pi vis parameter domain codomain -> do
        _ <- checkElab context domain Universe
        let extendedContext = extendContextType parameter domain context
        _ <- checkElab extendedContext codomain Universe
        pure (Pi vis parameter domain codomain, Universe)

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
                paramDomain <- freshMetaVar
                codomainMeta <- freshMetaVar
                let assumedPi = Pi Explicit (Identifier "_") paramDomain codomainMeta
                modify (\s -> s { metaSubst = Map.insert i assumedPi (metaSubst s) })
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
        _ <- checkElab context parameterType Universe
        let extendedContext = extendContextType parameter parameterType context
        (bodyExpr, bodyType) <- synthesizeElab extendedContext body
        pure (Lambda vis parameter (Just parameterType) bodyExpr, Pi vis parameter parameterType bodyType)

    Lambda _ _ Nothing _ ->
        lift $ Left (CannotSynthesizeType expression)

checkElab :: Context -> Expression -> Expression -> Elab Expression
checkElab context expression expectedType = do
    zonkedExpected <- zonk expectedType
    let env = contextValues context
        whnfExpected = evaluateWeakHeadNormalForm env zonkedExpected
    case (expression, whnfExpected) of
        (Hole _, _) ->
            freshMetaVar

        -- Explicit lambda checking against explicit Pi
        (Lambda Explicit parameter maybeDeclaredType body, Pi Explicit binder domain codomain) -> do
            case maybeDeclaredType of
                Just declaredType -> do
                    _ <- checkElab context declaredType Universe
                    unify env declaredType domain
                Nothing -> pure ()
            let targetParameter = parameter
                renamedBody = body
                substitutedCodomain = substitute binder (Variable targetParameter) codomain
                extendedContext = extendContextType targetParameter domain context
            elaboratedBody <- checkElab extendedContext renamedBody substitutedCodomain
            pure (Lambda Explicit targetParameter (Just domain) elaboratedBody)

        -- Implicit lambda checking against implicit Pi
        (Lambda Implicit parameter maybeDeclaredType body, Pi Implicit binder domain codomain) -> do
            case maybeDeclaredType of
                Just declaredType -> do
                    _ <- checkElab context declaredType Universe
                    unify env declaredType domain
                Nothing -> pure ()
            let targetParameter = parameter
                renamedBody = body
                substitutedCodomain = substitute binder (Variable targetParameter) codomain
                extendedContext = extendContextType targetParameter domain context
            elaboratedBody <- checkElab extendedContext renamedBody substitutedCodomain
            pure (Lambda Implicit targetParameter (Just domain) elaboratedBody)

        -- Automatic implicit lambda insertion: term checked against an Implicit Pi
        (otherExpr, Pi Implicit binder domain codomain) -> do
            let extendedContext = extendContextType binder domain context
            elaboratedBody <- checkElab extendedContext otherExpr codomain
            pure (Lambda Implicit binder (Just domain) elaboratedBody)

        (Lambda _ _ _ _, notPiType) ->
            lift $ Left (ExpectedFunctionType notPiType)

        (otherExpression, _) -> do
            (elabExpr, synthesizedType) <- synthesizeElab context otherExpression
            unify env synthesizedType zonkedExpected
            pure elabExpr

synthesize :: Context -> Expression -> Either TypeError (Expression, Expression)
synthesize context rawExpr =
    evalStateT (do
        exprWithMetas <- instantiateHoles rawExpr
        (elabExpr, rawType) <- synthesizeElab context exprWithMetas
        zonkedType <- zonk rawType
        zonkedExpr <- zonk elabExpr
        pure (zonkedExpr, zonkedType)
    ) (ElabState 0 Map.empty)

check :: Context -> Expression -> Expression -> Either TypeError Expression
check context rawExpr expectedType =
    evalStateT (do
        exprWithMetas <- instantiateHoles rawExpr
        expTypeWithMetas <- instantiateHoles expectedType
        elabExpr <- checkElab context exprWithMetas expTypeWithMetas
        zonk elabExpr
    ) (ElabState 0 Map.empty)

checkDefinition :: Context -> Identifier -> Maybe Expression -> Expression -> Either TypeError (Context, Expression)
checkDefinition context name maybeDeclaredType bodyTerm =
    evalStateT (do
        (zonkedBody, finalType) <- case maybeDeclaredType of
            Just declaredType -> do
                declWithMetas <- instantiateHoles declaredType
                _ <- checkElab context declWithMetas Universe
                zonkedDeclType <- zonk declWithMetas
                bodyWithMetas <- instantiateHoles bodyTerm
                elabBody <- checkElab context bodyWithMetas zonkedDeclType
                zonkedBodyTerm <- zonk elabBody
                pure (zonkedBodyTerm, zonkedDeclType)
            Nothing -> do
                bodyWithMetas <- instantiateHoles bodyTerm
                (elabBody, rawType) <- synthesizeElab context bodyWithMetas
                zonkedType <- zonk rawType
                zonkedBodyTerm <- zonk elabBody
                pure (zonkedBodyTerm, zonkedType)
        let updatedContext = extendContextDefinition name finalType zonkedBody context
        pure (updatedContext, finalType)
    ) (ElabState 0 Map.empty)

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
    CannotSynthesizeType term ->
        "Cannot synthesize type for unannotated expression:\n  "
            <> prettyExpression term
            <> "\nProvide an explicit type annotation: (term : Type)"
    OccursCheckFailed i term ->
        "Occurs check failed: ?" <> Text.pack (show i) <> " occurs in " <> prettyExpression term
    UnsolvedMetavariable i ->
        "Unsolved metavariable: ?" <> Text.pack (show i)
