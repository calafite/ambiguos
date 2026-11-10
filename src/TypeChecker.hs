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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
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
        Just expressionType ->
            pure expressionType
        Nothing ->
            Left (UnboundVariable identifier)

identityType :: Expression
identityType =
    Pi
        (Identifier "A")
        Universe
        ( Pi
            (Identifier "_")
            (Variable (Identifier "A"))
            (Pi (Identifier "_") (Variable (Identifier "A")) Universe)
        )

reflexivityType :: Expression
reflexivityType =
    Pi
        (Identifier "A")
        Universe
        ( Pi
            (Identifier "x")
            (Variable (Identifier "A"))
            ( Application
                ( Application
                    (Application Identity (Variable (Identifier "A")))
                    (Variable (Identifier "x"))
                )
                (Variable (Identifier "x"))
            )
        )

jType :: Expression
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
                ( Application
                    ( Application
                        (Application Identity (Variable (Identifier "A")))
                        (Variable (Identifier "x"))
                    )
                    (Variable (Identifier "y"))
                )
                Universe
            )

    baseCaseType =
        Application
            (Application (Variable (Identifier "P")) (Variable (Identifier "x")))
            ( Application
                (Application Reflexivity (Variable (Identifier "A")))
                (Variable (Identifier "x"))
            )

    proofType =
        Application
            ( Application
                (Application Identity (Variable (Identifier "A")))
                (Variable (Identifier "x"))
            )
            (Variable (Identifier "y"))

    codomainType =
        Application
            (Application (Variable (Identifier "P")) (Variable (Identifier "y")))
            (Variable (Identifier "p"))

abortType :: Expression
abortType =
    Pi
        (Identifier "A")
        Universe
        (Pi (Identifier "_") VoidType (Variable (Identifier "A")))

succType :: Expression
succType =
    Pi (Identifier "_") NatType NatType

natRecType :: Expression
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

synthesize :: Context -> Expression -> Either TypeError Expression
synthesize context expression = case expression of
    Variable identifier ->
        lookupContext identifier context
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
    Annotation term annotationType -> do
        check context annotationType Universe
        check context term annotationType
        pure annotationType
    Pi parameter domain codomain -> do
        check context domain Universe
        let extendedContext = extendContextType parameter domain context
        check extendedContext codomain Universe
        pure Universe
    Application function argument -> do
        functionType <- synthesize context function
        case evaluateWeakHeadNormalForm (contextValues context) functionType of
            Pi parameter domain codomain -> do
                check context argument domain
                pure (substitute parameter argument codomain)
            nonFunctionType ->
                Left (ExpectedFunctionType nonFunctionType)
    Lambda parameter (Just parameterType) body -> do
        check context parameterType Universe
        let extendedContext = extendContextType parameter parameterType context
        bodyType <- synthesize extendedContext body
        pure (Pi parameter parameterType bodyType)
    Lambda _ Nothing _ ->
        Left (CannotSynthesizeType expression)

check :: Context -> Expression -> Expression -> Either TypeError ()
check context expression expectedType =
    case (expression, evaluateWeakHeadNormalForm (contextValues context) expectedType) of
        (Lambda parameter maybeDeclaredType body, Pi binder domain codomain) -> do
            case maybeDeclaredType of
                Just declaredType -> do
                    check context declaredType Universe
                    if areDefinitionallyEqual (contextValues context) declaredType domain
                        then pure ()
                        else
                            Left
                                TypeMismatch
                                    { expectedType = domain
                                    , actualType = normalize (contextValues context) declaredType
                                    }
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
            check extendedContext renamedBody substitutedCodomain
        (Lambda _ _ _, notPiType) ->
            Left (ExpectedFunctionType notPiType)
        (otherExpression, expectedTypeWhnf) -> do
            synthesizedType <- synthesize context otherExpression
            if areDefinitionallyEqual (contextValues context) synthesizedType expectedTypeWhnf
                then pure ()
                else
                    Left
                        TypeMismatch
                            { expectedType = expectedTypeWhnf
                            , actualType = normalize (contextValues context) synthesizedType
                            }

checkDefinition :: Context -> Identifier -> Maybe Expression -> Expression -> Either TypeError (Context, Expression)
checkDefinition context name maybeDeclaredType bodyTerm = case maybeDeclaredType of
    Just declaredType -> do
        check context declaredType Universe
        check context bodyTerm declaredType
        let updatedContext = extendContextDefinition name declaredType bodyTerm context
        pure (updatedContext, declaredType)
    Nothing -> do
        synthesizedType <- synthesize context bodyTerm
        let updatedContext = extendContextDefinition name synthesizedType bodyTerm context
        pure (updatedContext, synthesizedType)

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
