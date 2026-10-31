module Evaluation
  ( evaluateWeakHeadNormalForm
  , normalize
  , areDefinitionallyEqual
  ) where

import AST (Expression (..), Identifier)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Substitution (alphaEquivalent, substitute)

evaluateWeakHeadNormalForm :: Map Identifier Expression -> Expression -> Expression
evaluateWeakHeadNormalForm environment expression =
  case expression of
    Variable identifier ->
      case Map.lookup identifier environment of
        Just value ->
          evaluateWeakHeadNormalForm environment value
        Nothing ->
          Variable identifier

    Annotation term _annotationType ->
      evaluateWeakHeadNormalForm environment term

    Application function argument ->
      case evaluateWeakHeadNormalForm environment function of
        Lambda parameter body ->
          evaluateWeakHeadNormalForm environment (substitute parameter argument body)
        neutralFunction ->
          Application neutralFunction argument

    Universe ->
      Universe

    Lambda parameter body ->
      Lambda parameter body

    Pi parameter domain codomain ->
      Pi parameter domain codomain

normalize :: Map Identifier Expression -> Expression -> Expression
normalize environment expression =
  case evaluateWeakHeadNormalForm environment expression of
    Variable identifier ->
      Variable identifier

    Universe ->
      Universe

    Lambda parameter body ->
      Lambda parameter (normalize environment body)

    Application function argument ->
      Application (normalize environment function) (normalize environment argument)

    Pi parameter domain codomain ->
      Pi parameter (normalize environment domain) (normalize environment codomain)

    Annotation term _annotationType ->
      normalize environment term

areDefinitionallyEqual :: Map Identifier Expression -> Expression -> Expression -> Bool
areDefinitionallyEqual environment leftExpression rightExpression =
  alphaEquivalent (normalize environment leftExpression) (normalize environment rightExpression)
