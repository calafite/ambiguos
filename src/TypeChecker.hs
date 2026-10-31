{-# LANGUAGE OverloadedStrings #-}

module TypeChecker
  ( TypeError (..)
  , Context
  , emptyContext
  , extendContext
  , synthesize
  , check
  , renderTypeError
  ) where

import AST (Expression (..), Identifier (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Evaluation (areDefinitionallyEqual, evaluateWeakHeadNormalForm, normalize)
import Substitution (freeVariables, freshIdentifier, substitute)

data TypeError
  = UnboundVariable Identifier
  | TypeMismatch
      { expectedType :: Expression
      , actualType   :: Expression
      }
  | ExpectedFunctionType
      { actualType :: Expression
      }
  | CannotSynthesizeType Expression
  deriving (Eq, Show)

newtype Context = Context
  { unContext :: Map Identifier Expression
  } deriving (Eq, Show)

emptyContext :: Context
emptyContext = Context Map.empty

extendContext :: Identifier -> Expression -> Context -> Context
extendContext identifier expressionType (Context currentBindings) =
  Context (Map.insert identifier expressionType currentBindings)

lookupContext :: Identifier -> Context -> Either TypeError Expression
lookupContext identifier (Context currentBindings) =
  case Map.lookup identifier currentBindings of
    Just expressionType ->
      pure expressionType
    Nothing ->
      Left (UnboundVariable identifier)

synthesize :: Context -> Expression -> Either TypeError Expression
synthesize context expression = case expression of
  Variable identifier ->
    lookupContext identifier context

  Universe ->
    pure Universe

  Annotation term annotationType -> do
    check context annotationType Universe
    check context term annotationType
    pure annotationType

  Pi parameter domain codomain -> do
    check context domain Universe
    let extendedContext = extendContext parameter domain context
    check extendedContext codomain Universe
    pure Universe

  Application function argument -> do
    functionType <- synthesize context function
    case evaluateWeakHeadNormalForm functionType of
      Pi parameter domain codomain -> do
        check context argument domain
        pure (substitute parameter argument codomain)
      nonFunctionType ->
        Left (ExpectedFunctionType nonFunctionType)

  Lambda _ _ ->
    Left (CannotSynthesizeType expression)

check :: Context -> Expression -> Expression -> Either TypeError ()
check context expression expectedType =
  case (expression, evaluateWeakHeadNormalForm expectedType) of
    (Lambda parameter body, Pi binder domain codomain) -> do
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
            extendContext targetParameter domain context
      check extendedContext renamedBody substitutedCodomain

    (Lambda _ _, notPiType) ->
      Left (ExpectedFunctionType notPiType)

    (otherExpression, expectedTypeWhnf) -> do
      synthesizedType <- synthesize context otherExpression
      if areDefinitionallyEqual synthesizedType expectedTypeWhnf
        then pure ()
        else
          Left
            TypeMismatch
              { expectedType = expectedTypeWhnf
              , actualType   = normalize synthesizedType
              }

renderTypeError :: TypeError -> Text
renderTypeError typeError = case typeError of
  UnboundVariable (Identifier name) ->
    "Unbound variable: '" <> name <> "'"
  TypeMismatch expected actual ->
    "Type mismatch:\n  Expected: "
      <> Text.pack (show expected)
      <> "\n  Actual:   "
      <> Text.pack (show actual)
  ExpectedFunctionType actual ->
    "Expected a function (Pi) type, but encountered:\n  "
      <> Text.pack (show actual)
  CannotSynthesizeType term ->
    "Cannot synthesize type for unannotated expression:\n  "
      <> Text.pack (show term)
      <> "\nProvide an explicit type annotation: (term : Type)"
