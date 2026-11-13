{-# LANGUAGE OverloadedStrings #-}

module Pretty (
    PrettyConfig (..),
    prettyExpression,
    prettyExpressionWith,
    prettyIdentifier,
    prettyWithPrecedence,
) where

import AST (CaseBranch (..), Expression (..), Identifier (..), Visibility (..))
import Control.Applicative ((<|>))
import Data.Text (Text)
import qualified Data.Text as Text

data Precedence
    = TopLevelPrecedence
    | AnnotationPrecedence
    | LambdaPrecedence
    | ArrowPrecedence
    | InfixPrecedence
    | ApplicationPrecedence
    | AtomicPrecedence
    deriving (Eq, Ord, Show)

-- | Configuration for pretty-printing expressions.
data PrettyConfig = PrettyConfig
    { prettyShowImplicits :: !Bool
    } deriving (Eq, Show)

-- | Default configuration: implicit arguments are shown.
defaultPrettyConfig :: PrettyConfig
defaultPrettyConfig = PrettyConfig True

-- | Pretty-print an expression with the default configuration.
prettyExpression :: Expression -> Text
prettyExpression = prettyExpressionWith defaultPrettyConfig

-- | Pretty-print an expression with a custom configuration.
prettyExpressionWith :: PrettyConfig -> Expression -> Text
prettyExpressionWith config = prettyWithConfig config TopLevelPrecedence

-- | Pretty-print an expression at a given precedence with the default config.
prettyWithPrecedence :: Precedence -> Expression -> Text
prettyWithPrecedence = prettyWithConfig defaultPrettyConfig

parenthesizeIf :: Bool -> Text -> Text
parenthesizeIf True text = "(" <> text <> ")"
parenthesizeIf False text = text

prettyIdentifier :: Identifier -> Text
prettyIdentifier ident@(Identifier name)
    | isSymbolic ident = "(" <> name <> ")"
    | otherwise = name

isSymbolic :: Identifier -> Bool
isSymbolic (Identifier name) =
    case Text.uncons name of
        Just (c, _) -> c `elem` ("+-*/<>=!&|$%^~." :: String)
        Nothing -> False

peanoToInteger :: Expression -> Maybe Integer
peanoToInteger Zero = Just 0
peanoToInteger (Application _ Succ rest) = do
    n <- peanoToInteger rest
    pure (n + 1)
peanoToInteger (Located _ e) = peanoToInteger e
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
peanoListToElements (Located _ e) = peanoListToElements e
peanoListToElements _ = Nothing

churchListToElements :: Expression -> Maybe [Expression]
churchListToElements (Located _ e) = churchListToElements e
churchListToElements (Lambda _ _ _ (Lambda _ n _ (Lambda _ c (Just (Pi _ _ _ _)) body))) =
    decode body
  where
    decode (Variable v) | v == n = Just []
    decode (Application _ (Application _ (Variable v) x) rest) | v == c = do
        xs <- decode rest
        pure (x : xs)
    decode _ = Nothing
churchListToElements _ = Nothing

prettyWithConfig :: PrettyConfig -> Precedence -> Expression -> Text
prettyWithConfig config currentPrecedence expression =
    case peanoToInteger expression of
        Just n -> Text.pack (show n)
        Nothing -> case peanoListToElements expression <|> churchListToElements expression of
            Just elems ->
                "[" <> Text.intercalate ", " (map (prettyWithConfig config TopLevelPrecedence) elems) <> "]"
            Nothing -> case expression of
                Located _ e ->
                    prettyWithConfig config currentPrecedence e
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
                    let bodyText = prettyWithConfig config TopLevelPrecedence body
                        rendered = "\\" <> prettyIdentifier parameter <> " -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Lambda Implicit parameter Nothing body ->
                    let bodyText = prettyWithConfig config TopLevelPrecedence body
                        rendered = "\\{" <> prettyIdentifier parameter <> "} -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Lambda Explicit parameter (Just parameterType) body ->
                    let typeText = prettyWithConfig config TopLevelPrecedence parameterType
                        bodyText = prettyWithConfig config TopLevelPrecedence body
                        rendered = "\\(" <> prettyIdentifier parameter <> " : " <> typeText <> ") -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Lambda Implicit parameter (Just parameterType) body ->
                    let typeText = prettyWithConfig config TopLevelPrecedence parameterType
                        bodyText = prettyWithConfig config TopLevelPrecedence body
                        rendered = "\\{" <> prettyIdentifier parameter <> " : " <> typeText <> "} -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Annotation term annotationType ->
                    let termText = prettyWithConfig config ArrowPrecedence term
                        typeText = prettyWithConfig config TopLevelPrecedence annotationType
                        rendered = termText <> " : " <> typeText
                     in parenthesizeIf (currentPrecedence > AnnotationPrecedence) rendered
                Application Explicit function argument ->
                    case function of
                        Application Explicit (Variable op) a1
                            | isSymbolic op ->
                                let (Identifier opName) = op
                                    a1Text = prettyWithConfig config InfixPrecedence a1
                                    a2Text = prettyWithConfig config ApplicationPrecedence argument
                                 in parenthesizeIf (currentPrecedence > InfixPrecedence)
                                        (a1Text <> " " <> opName <> " " <> a2Text)
                        _ ->
                            let functionText = prettyWithConfig config ApplicationPrecedence function
                                argumentText = prettyWithConfig config AtomicPrecedence argument
                             in parenthesizeIf (currentPrecedence > ApplicationPrecedence)
                                    (functionText <> " " <> argumentText)
                Application Implicit function argument ->
                    if prettyShowImplicits config
                        then
                            let functionText = prettyWithConfig config ApplicationPrecedence function
                                argumentText = prettyWithConfig config TopLevelPrecedence argument
                                rendered = functionText <> " {" <> argumentText <> "}"
                             in parenthesizeIf (currentPrecedence > ApplicationPrecedence) rendered
                        else prettyWithConfig config currentPrecedence function
                Pi Explicit (Identifier "_") domain codomain ->
                    let domainText = prettyWithConfig config ApplicationPrecedence domain
                        codomainText = prettyWithConfig config ArrowPrecedence codomain
                        rendered = domainText <> " -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
                Pi Explicit parameter domain codomain ->
                    let domainText = prettyWithConfig config TopLevelPrecedence domain
                        codomainText = prettyWithConfig config ArrowPrecedence codomain
                        rendered = "(" <> prettyIdentifier parameter <> " : " <> domainText <> ") -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
                Pi Implicit parameter domain codomain ->
                    let domainText = prettyWithConfig config TopLevelPrecedence domain
                        codomainText = prettyWithConfig config ArrowPrecedence codomain
                        rendered = "{" <> prettyIdentifier parameter <> " : " <> domainText <> "} -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > ArrowPrecedence) rendered
                Let param Nothing defExpr body ->
                    let defText = prettyWithConfig config TopLevelPrecedence defExpr
                        bodyText = prettyWithConfig config TopLevelPrecedence body
                        rendered = "let " <> prettyIdentifier param <> " = " <> defText <> " in " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Let param (Just paramType) defExpr body ->
                    let typeText = prettyWithConfig config TopLevelPrecedence paramType
                        defText = prettyWithConfig config TopLevelPrecedence defExpr
                        bodyText = prettyWithConfig config TopLevelPrecedence body
                        rendered = "let " <> prettyIdentifier param <> " : " <> typeText <> " = " <> defText <> " in " <> bodyText
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
                Case target branches ->
                    let targetText = prettyWithConfig config TopLevelPrecedence target
                        formatBranch (CaseBranch con vars body) =
                            let headStr = Text.unwords (prettyIdentifier con : map prettyIdentifier vars)
                             in headStr <> " -> " <> prettyWithConfig config TopLevelPrecedence body
                        branchesText = Text.intercalate " ; " (map formatBranch branches)
                        rendered = "case " <> targetText <> " of { " <> branchesText <> " }"
                     in parenthesizeIf (currentPrecedence > LambdaPrecedence) rendered
