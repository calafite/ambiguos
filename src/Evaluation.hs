module Evaluation
  ( evaluateWeakHeadNormalForm
  , normalize
  , areDefinitionallyEqual
  ) where

import AST (Expression (..))
import Substitution (alphaEquivalent, substitute)

evaluateWeakHeadNormalForm :: Expression -> Expression
evaluateWeakHeadNormalForm expression =
  case expression of
    Annotation term _annotationType ->
      evaluateWeakHeadNormalForm term

    Application function argument ->
      case evaluateWeakHeadNormalForm function of
        Lambda parameter body ->
          evaluateWeakHeadNormalForm (substitute parameter argument body)
        neutralFunction ->
          Application neutralFunction argument

    Variable identifier ->
      Variable identifier

    Universe ->
      Universe

    Lambda parameter body ->
      Lambda parameter body

    Pi parameter domain codomain ->
      Pi parameter domain codomain

normalize :: Expression -> Expression
normalize expression =
  case evaluateWeakHeadNormalForm expression of
    Variable identifier ->
      Variable identifier

    Universe ->
      Universe

    Lambda parameter body ->
      Lambda parameter (normalize body)

    Application function argument ->
      Application (normalize function) (normalize argument)

    Pi parameter domain codomain ->
      Pi parameter (normalize domain) (normalize codomain)

    Annotation term _annotationType ->
      normalize term

areDefinitionallyEqual :: Expression -> Expression -> Bool
areDefinitionallyEqual leftExpression rightExpression =
  alphaEquivalent (normalize leftExpression) (normalize rightExpression)
