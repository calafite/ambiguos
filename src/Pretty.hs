{-# LANGUAGE OverloadedStrings #-}

module Pretty (
    prettyExpression,
    prettyIdentifier,
) where

import AST (Expression (..), Identifier (..), Visibility (..))
import Control.Applicative ((<|>))
import Data.Text (Text)
import qualified Data.Text as Text

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

peanoToInteger :: Expression -> Maybe Integer
peanoToInteger Zero = Just 0
peanoToInteger (Application _ Succ rest) = do
    n <- peanoToInteger rest
    pure (n + 1)
peanoToInteger _ = Nothing

peanoListToElements :: Expression -> Maybe [Expression]
peanoListToElements (Variable (Identifier "nil")) = Just []
peanoListToElements (Application Implicit (Variable (Identifier "nil")) _) = Just []
peanoListToElements (Application Explicit (Application Explicit (Application Implicit (Variable (Identifier "cons")) _) x) rest) = do
    xs <- peanoListToElements rest
    pure (x : xs)
peanoListToElements (Application Explicit (Application Explicit (Variable (Identifier "cons")) x) rest) = do
    xs <- peanoListToElements rest
    pure (x : xs)
peanoListToElements _ = Nothing

churchListToElements :: Expression -> Maybe [Expression]
churchListToElements (Lambda _ _ _ (Lambda _ n _ (Lambda _ c (Just (Pi _ _ _ _)) body))) =
    decode body
  where
    decode (Variable v) | v == n = Just []
    decode (Application _ (Application _ (Variable v) x) rest) | v == c = do
        xs <- decode rest
        pure (x : xs)
    decode _ = Nothing
churchListToElements _ = Nothing

prettyExpression :: Expression -> Text
prettyExpression = prettyWithPrecedence TopLevelPrecedence

prettyWithPrecedence :: Precedence -> Expression -> Text
prettyWithPrecedence currentPrecedence expression =
    case peanoToInteger expression of
        Just n -> Text.pack (show n)
        Nothing -> case peanoListToElements expression <|> churchListToElements expression of
            Just elems ->
                "[" <> Text.intercalate ", " (map prettyExpression elems) <> "]"
            Nothing -> case expression of
                Variable identifier ->
                    prettyIdentifier identifier
                Universe (-1) -> "Type"
                Universe 0 -> "Type 0"
                Universe n -> "Type " <> Text.pack (show n)
                Identity -> "Id"
                Reflexivity -> "refl"
                J -> "J"
                VoidType -> "Void"
                Abort -> "abort"
                NatType -> "Nat"
                Zero -> "zero"
                Succ -> "successor"
                NatRec -> "natRec"
                Hole Nothing -> "?"
                Hole (Just (Identifier name)) -> "?" <> name
                MetaVar i -> "?" <> Text.pack (show i)
                Lambda Explicit parameter Nothing body ->
                    let bodyText = prettyWithPrecedence TopLevelPrecedence body
                        rendered = "\\" <> prettyIdentifier parameter <> " -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Lambda Implicit parameter Nothing body ->
                    let bodyText = prettyWithPrecedence TopLevelPrecedence body
                        rendered = "\\{" <> prettyIdentifier parameter <> "} -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Lambda Explicit parameter (Just parameterType) body ->
                    let typeText = prettyWithPrecedence TopLevelPrecedence parameterType
                        bodyText = prettyWithPrecedence TopLevelPrecedence body
                        rendered = "\\(" <> prettyIdentifier parameter <> " : " <> typeText <> ") -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Lambda Implicit parameter (Just parameterType) body ->
                    let typeText = prettyWithPrecedence TopLevelPrecedence parameterType
                        bodyText = prettyWithPrecedence TopLevelPrecedence body
                        rendered = "\\{" <> prettyIdentifier parameter <> " : " <> typeText <> "} -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Annotation term annotationType ->
                    let termText = prettyWithPrecedence ArrowPrecedence term
                        typeText = prettyWithPrecedence TopLevelPrecedence annotationType
                        rendered = termText <> " : " <> typeText
                     in parenthesizeIf (currentPrecedence > AnnotationPrecedence) rendered
                Application Explicit function argument ->
                    let functionText = prettyWithPrecedence ApplicationPrecedence function
                        argumentText = prettyWithPrecedence AtomicPrecedence argument
                        rendered = functionText <> " " <> argumentText
                     in parenthesizeIf (currentPrecedence > ApplicationPrecedence) rendered
                Application Implicit function argument ->
                    let functionText = prettyWithPrecedence ApplicationPrecedence function
                        argumentText = prettyWithPrecedence TopLevelPrecedence argument
                        rendered = functionText <> " {" <> argumentText <> "}"
                     in parenthesizeIf (currentPrecedence > ApplicationPrecedence) rendered
                Pi Explicit (Identifier "_") domain codomain ->
                    let domainText = prettyWithPrecedence ApplicationPrecedence domain
                        codomainText = prettyWithPrecedence ArrowPrecedence codomain
                        rendered = domainText <> " -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
                Pi Explicit parameter domain codomain ->
                    let domainText = prettyWithPrecedence TopLevelPrecedence domain
                        codomainText = prettyWithPrecedence ArrowPrecedence codomain
                        rendered = "(" <> prettyIdentifier parameter <> " : " <> domainText <> ") -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
                Pi Implicit parameter domain codomain ->
                    let domainText = prettyWithPrecedence TopLevelPrecedence domain
                        codomainText = prettyWithPrecedence ArrowPrecedence codomain
                        rendered = "{" <> prettyIdentifier parameter <> " : " <> domainText <> "} -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
