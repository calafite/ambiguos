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

import AST (Expression (..), Identifier (..))
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
        Nothing -> Left (UnboundVariable identifier)

data ElabState = ElabState
    { nextMetaId :: !Int
    , metaSubst :: !(Map Int Expression)
    }

type Elab a = StateT ElabState (Either TypeError) a

catchElab :: Elab a -> (TypeError -> Elab a) -> Elab a
catchElab (StateT action) handler = StateT $ \s ->
    case action s of
        Left err -> runStateT (handler err) s
        Right (res, s') -> Right (res, s')

tryElab :: Elab a -> Elab a -> Elab a
tryElab primary fallback = catchElab primary (\_ -> fallback)

freshMetaVar :: Elab Expression
freshMetaVar = do
    idx <- gets nextMetaId
    modify (\s -> s{nextMetaId = idx + 1})
    pure (MetaVar idx)

instantiateHoles :: Expression -> Elab Expression
instantiateHoles expr = case expr of
    Hole _ -> freshMetaVar
    Application f a -> Application <$> instantiateHoles f <*> instantiateHoles a
    Lambda p ty body -> Lambda p <$> traverse instantiateHoles ty <*> instantiateHoles body
    Pi p d c -> Pi p <$> instantiateHoles d <*> instantiateHoles c
    Annotation t ty -> Annotation <$> instantiateHoles t <*> instantiateHoles ty
    other -> pure other

zonk :: Expression -> Elab Expression
zonk expr = do
    substMap <- gets metaSubst
    case expr of
        MetaVar i ->
            case Map.lookup i substMap of
                Just resolved -> zonk resolved
                Nothing -> pure (MetaVar i)
        Application f a -> Application <$> zonk f <*> zonk a
        Lambda p ty body -> Lambda p <$> traverse zonk ty <*> zonk body
        Pi p d c -> Pi p <$> zonk d <*> zonk c
        Annotation t ty -> Annotation <$> zonk t <*> zonk ty
        other -> pure other

occursIn :: Int -> Expression -> Bool
occursIn i expr = case expr of
    MetaVar j -> i == j
    Application f a -> occursIn i f || occursIn i a
    Lambda _ ty body -> maybe False (occursIn i) ty || occursIn i body
    Pi _ d c -> occursIn i d || occursIn i c
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
        (Application f1 a1, Application f2 a2) ->
            tryElab
                ( do
                    unify env f1 f2
                    unify env a1 a2
                )
                (unfoldAndRetry z1 z2)
        (Pi p1 d1 c1, Pi p2 d2 c2) ->
            tryElab
                ( do
                    unify env d1 d2
                    if p1 == p2
                        then unify env c1 c2
                        else do
                            let fresh = freshIdentifier p1 (Set.union (freeVariables c1) (freeVariables c2))
                            unify env (substitute p1 (Variable fresh) c1) (substitute p2 (Variable fresh) c2)
                )
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
                    else
                        if areDefinitionallyEqual env w1 w2
                            then pure ()
                            else lift $ Left (TypeMismatch t2 t1)

    bindMeta :: Int -> Expression -> Elab ()
    bindMeta i term
        | occursIn i term = lift $ Left (OccursCheckFailed i term)
        | otherwise = modify (\s -> s{metaSubst = Map.insert i term (metaSubst s)})

identityType, reflexivityType, jType, abortType, succType, natRecType :: Expression
identityType =
    Pi
        (Identifier "A")
        Universe
        ( Pi
            (Identifier "_")
            (Variable (Identifier "A"))
            (Pi (Identifier "_") (Variable (Identifier "A")) Universe)
        )
reflexivityType =
    Pi
        (Identifier "A")
        Universe
        ( Pi
            (Identifier "x")
            (Variable (Identifier "A"))
            ( Application
                (Application (Application Identity (Variable (Identifier "A"))) (Variable (Identifier "x")))
                (Variable (Identifier "x"))
            )
        )
jType =
    Pi (Identifier "A") Universe
        $ Pi (Identifier "x") (Variable (Identifier "A"))
        $ Pi (Identifier "P") motiveType
        $ Pi (Identifier "d") baseCaseType
        $ Pi (Identifier "y") (Variable (Identifier "A"))
        $ Pi (Identifier "p") proofType codomainType
  where
    motiveType =
        Pi
            (Identifier "y")
            (Variable (Identifier "A"))
            ( Pi
                (Identifier "_")
                (Application (Application (Application Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y")))
                Universe
            )
    baseCaseType =
        Application
            (Application (Variable (Identifier "P")) (Variable (Identifier "x")))
            (Application (Application Reflexivity (Variable (Identifier "A"))) (Variable (Identifier "x")))
    proofType =
        Application (Application (Application Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y"))
    codomainType =
        Application (Application (Variable (Identifier "P")) (Variable (Identifier "y"))) (Variable (Identifier "p"))
abortType =
    Pi
        (Identifier "A")
        Universe
        (Pi (Identifier "_") VoidType (Variable (Identifier "A")))
succType =
    Pi (Identifier "_") NatType NatType
natRecType =
    Pi (Identifier "P") pType
        $ Pi (Identifier "z") zType
        $ Pi (Identifier "s") sType
        $ Pi (Identifier "n") NatType codomainType
  where
    pType = Pi (Identifier "_") NatType Universe
    zType = Application (Variable (Identifier "P")) Zero
    nVar = Variable (Identifier "n")
    pn = Application (Variable (Identifier "P")) nVar
    psuccn = Application (Variable (Identifier "P")) (Application Succ nVar)
    sType = Pi (Identifier "n") NatType (Pi (Identifier "_") pn psuccn)
    codomainType = Application (Variable (Identifier "P")) nVar

synthesizeElab :: Context -> Expression -> Elab Expression
synthesizeElab context expression = case expression of
    Variable identifier -> lift (lookupContext identifier context)
    Universe -> pure Universe
    Identity -> pure identityType
    Reflexivity -> pure reflexivityType
    J -> pure jType
    VoidType -> pure Universe
    Abort -> pure abortType
    NatType -> pure Universe
    Zero -> pure NatType
    Succ -> pure succType
    NatRec -> pure natRecType
    MetaVar i -> do
        substMap <- gets metaSubst
        case Map.lookup i substMap of
            Just term -> synthesizeElab context term
            Nothing -> freshMetaVar
    Hole _ -> freshMetaVar
    Annotation term annotationType -> do
        checkElab context annotationType Universe
        checkElab context term annotationType
        pure annotationType
    Pi parameter domain codomain -> do
        checkElab context domain Universe
        let extendedContext = extendContextType parameter domain context
        checkElab extendedContext codomain Universe
        pure Universe
    Application function argument -> do
        functionType <- synthesizeElab context function
        zonkedType <- zonk functionType
        case evaluateWeakHeadNormalForm (contextValues context) zonkedType of
            Pi parameter domain codomain -> do
                checkElab context argument domain
                zonkedArg <- zonk argument
                pure (substitute parameter zonkedArg codomain)
            MetaVar i -> do
                paramDomain <- freshMetaVar
                codomainMeta <- freshMetaVar
                let assumedPi = Pi (Identifier "_") paramDomain codomainMeta
                modify (\s -> s{metaSubst = Map.insert i assumedPi (metaSubst s)})
                checkElab context argument paramDomain
                zonkedArg <- zonk argument
                pure (substitute (Identifier "_") zonkedArg codomainMeta)
            nonFunctionType ->
                lift $ Left (ExpectedFunctionType nonFunctionType)
    Lambda parameter (Just parameterType) body -> do
        checkElab context parameterType Universe
        let extendedContext = extendContextType parameter parameterType context
        bodyType <- synthesizeElab extendedContext body
        pure (Pi parameter parameterType bodyType)
    Lambda _ Nothing _ ->
        lift $ Left (CannotSynthesizeType expression)

checkElab :: Context -> Expression -> Expression -> Elab ()
checkElab context expression expectedType = do
    zonkedExpected <- zonk expectedType
    let env = contextValues context
        whnfExpected = evaluateWeakHeadNormalForm env zonkedExpected
    case (expression, whnfExpected) of
        (Hole _, _) -> pure ()
        (Lambda parameter maybeDeclaredType body, Pi binder domain codomain) -> do
            case maybeDeclaredType of
                Just declaredType -> do
                    checkElab context declaredType Universe
                    unify env declaredType domain
                Nothing -> pure ()
            let targetParameter
                    | parameter == binder = parameter
                    | Set.member parameter (freeVariables codomain) =
                        freshIdentifier parameter (Set.unions [freeVariables body, freeVariables codomain])
                    | otherwise = parameter
                renamedBody
                    | targetParameter == parameter = body
                    | otherwise = substitute parameter (Variable targetParameter) body
                substitutedCodomain =
                    substitute binder (Variable targetParameter) codomain
                extendedContext =
                    extendContextType targetParameter domain context
            checkElab extendedContext renamedBody substitutedCodomain
        (Lambda _ _ _, notPiType) ->
            lift $ Left (ExpectedFunctionType notPiType)
        (otherExpression, _) -> do
            synthesizedType <- synthesizeElab context otherExpression
            unify env synthesizedType zonkedExpected

synthesize :: Context -> Expression -> Either TypeError (Expression, Expression)
synthesize context rawExpr =
    evalStateT
        ( do
            exprWithMetas <- instantiateHoles rawExpr
            rawType <- synthesizeElab context exprWithMetas
            zonkedType <- zonk rawType
            zonkedExpr <- zonk exprWithMetas
            pure (zonkedExpr, zonkedType)
        )
        (ElabState 0 Map.empty)

check :: Context -> Expression -> Expression -> Either TypeError Expression
check context rawExpr expectedType =
    evalStateT
        ( do
            exprWithMetas <- instantiateHoles rawExpr
            expTypeWithMetas <- instantiateHoles expectedType
            checkElab context exprWithMetas expTypeWithMetas
            zonkedExpr <- zonk exprWithMetas
            pure zonkedExpr
        )
        (ElabState 0 Map.empty)

checkDefinition :: Context -> Identifier -> Maybe Expression -> Expression -> Either TypeError (Context, Expression)
checkDefinition context name maybeDeclaredType bodyTerm =
    evalStateT
        ( do
            (zonkedBody, finalType) <- case maybeDeclaredType of
                Just declaredType -> do
                    declWithMetas <- instantiateHoles declaredType
                    checkElab context declWithMetas Universe
                    zonkedDeclType <- zonk declWithMetas
                    bodyWithMetas <- instantiateHoles bodyTerm
                    checkElab context bodyWithMetas zonkedDeclType
                    zonkedBodyTerm <- zonk bodyWithMetas
                    pure (zonkedBodyTerm, zonkedDeclType)
                Nothing -> do
                    bodyWithMetas <- instantiateHoles bodyTerm
                    rawType <- synthesizeElab context bodyWithMetas
                    zonkedType <- zonk rawType
                    zonkedBodyTerm <- zonk bodyWithMetas
                    pure (zonkedBodyTerm, zonkedType)
            let updatedContext = extendContextDefinition name finalType zonkedBody context
            pure (updatedContext, finalType)
        )
        (ElabState 0 Map.empty)

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
