{-# LANGUAGE OverloadedStrings #-}

module Pretty
  ( prettyExpression
  , prettyIdentifier
  ) where

import AST (Expression (..), Identifier (..))
import Data.Text (Text)

data Precedence
  = TopLevelPrecedence
  | AnnotationPrecedence
  | LambdaPrecedence
  | ArrowPrecedence
  | ApplicationPrecedence
  | AtomicPrecedence
  deriving (Eq, Ord, Show)

parenthesizeIf :: Bool -> Text -> Text
parenthesizeIf True text = "(" <> text <> ")"
parenthesizeIf False text = text

prettyIdentifier :: Identifier -> Text
prettyIdentifier (Identifier name) = name

prettyExpression :: Expression -> Text
prettyExpression = prettyWithPrecedence TopLevelPrecedence

prettyWithPrecedence :: Precedence -> Expression -> Text
prettyWithPrecedence currentPrecedence expression = case expression of
  Variable identifier ->
    prettyIdentifier identifier

  Universe ->
    "Type"

  Lambda parameter body ->
    let bodyText = prettyWithPrecedence TopLevelPrecedence body
        rendered = "\\" <> prettyIdentifier parameter <> " -> " <> bodyText
    in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered

  Annotation term annotationType ->
    let termText = prettyWithPrecedence ArrowPrecedence term
        typeText = prettyWithPrecedence TopLevelPrecedence annotationType
        rendered = termText <> " : " <> typeText
    in parenthesizeIf (currentPrecedence > AnnotationPrecedence) rendered

  Application function argument ->
    let functionText = prettyWithPrecedence ApplicationPrecedence function
        argumentText = prettyWithPrecedence AtomicPrecedence argument
        rendered = functionText <> " " <> argumentText
    in parenthesizeIf (currentPrecedence > ApplicationPrecedence) rendered

  Pi (Identifier "_") domain codomain ->
    let domainText = prettyWithPrecedence ApplicationPrecedence domain
        codomainText = prettyWithPrecedence ArrowPrecedence codomain
        rendered = domainText <> " -> " <> codomainText
    in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered

  Pi parameter domain codomain ->
    let domainText = prettyWithPrecedence TopLevelPrecedence domain
        codomainText = prettyWithPrecedence ArrowPrecedence codomain
        rendered = "(" <> prettyIdentifier parameter <> " : " <> domainText <> ") -> " <> codomainText
    in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
