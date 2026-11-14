{-# LANGUAGE OverloadedStrings #-}

module Pretty (
    PrettyConfig (..),
    prettyExpression,
    prettyExpressionWith,
    prettyIdentifier,
    prettyWithPrecedence,
    parenLeft,
    parenRight,
) where

import AST (Associativity (..), CaseBranch (..), Expression (..), Fixity (..), Identifier (..), Visibility (..))
import Control.Applicative ((<|>))
import Data.Text (Text)
import qualified Data.Text as Text
import Parser (FixityEnv, defaultFixityEnv, fixityOf)

data Precedence
    = TopLevelPrecedence
    | AnnotationPrecedence
    | LambdaPrecedence
    | ArrowPrecedence
    | ApplicationPrecedence
    | AtomicPrecedence
    deriving (Eq, Ord, Show)

precLevel :: Precedence -> Int
precLevel TopLevelPrecedence = 0
precLevel AnnotationPrecedence = 1
precLevel LambdaPrecedence = 2
precLevel ArrowPrecedence = 3
precLevel ApplicationPrecedence = 7
precLevel AtomicPrecedence = 10

-- | Configuration for pretty-printing expressions.
data PrettyConfig = PrettyConfig
    { prettyShowImplicits :: !Bool
    , prettyFixities    :: !FixityEnv
    } deriving (Eq, Show)

-- | Default configuration: implicit arguments are shown, default fixities.
defaultPrettyConfig :: PrettyConfig
defaultPrettyConfig = PrettyConfig True defaultFixityEnv

-- | Pretty-print an expression with the default configuration.
prettyExpression :: Expression -> Text
prettyExpression = prettyExpressionWith defaultPrettyConfig

-- | Pretty-print an expression with a custom configuration.
prettyExpressionWith :: PrettyConfig -> Expression -> Text
prettyExpressionWith config = prettyWithConfig config 0

-- | Pretty-print an expression at a given precedence with the default config.
prettyWithPrecedence :: PrettyConfig -> Precedence -> Expression -> Text
prettyWithPrecedence config = prettyWithConfig config . precLevel

-- | Internal pretty-printer working on a numeric precedence scale (0-10).
-- Higher numbers bind tighter. Operator precedences live in the same scale.
prettyWithConfig :: PrettyConfig -> Int -> Expression -> Text
prettyWithConfig config currentPrecedence expression =
    case peanoToInteger expression of
        Just n -> Text.pack (show n)
        Nothing -> case peanoListToElements expression <|> churchListToElements expression of
            Just elems ->
                "[" <> Text.intercalate ", " (map (prettyWithConfig config 0) elems) <> "]"
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
                    let bodyText = prettyWithConfig config 0 body
                        rendered = "\\" <> prettyIdentifier parameter <> " -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered
                Lambda Implicit parameter Nothing body ->
                    let bodyText = prettyWithConfig config 0 body
                        rendered = "\\{" <> prettyIdentifier parameter <> "} -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered
                Lambda Explicit parameter (Just parameterType) body ->
                    let typeText = prettyWithConfig config 0 parameterType
                        bodyText = prettyWithConfig config 0 body
                        rendered = "\\(" <> prettyIdentifier parameter <> " : " <> typeText <> ") -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered
                Lambda Implicit parameter (Just parameterType) body ->
                    let typeText = prettyWithConfig config 0 parameterType
                        bodyText = prettyWithConfig config 0 body
                        rendered = "\\{" <> prettyIdentifier parameter <> " : " <> typeText <> "} -> " <> bodyText
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered
                Annotation term annotationType ->
                    let termText = prettyWithConfig config (precLevel ArrowPrecedence) term
                        typeText = prettyWithConfig config 0 annotationType
                        rendered = termText <> " : " <> typeText
                     in parenthesizeIf (currentPrecedence > precLevel AnnotationPrecedence) rendered
                Application Explicit function argument ->
                    case function of
                        Application Explicit (Variable op) a1
                            | isSymbolic op ->
                                prettyInfixApp config (prettyFixities config) op a1 argument currentPrecedence
                        _ ->
                            let functionText = prettyWithConfig config (precLevel ApplicationPrecedence) function
                                argumentText = prettyWithConfig config (precLevel AtomicPrecedence) argument
                             in parenthesizeIf (currentPrecedence > precLevel ApplicationPrecedence)
                                    (functionText <> " " <> argumentText)
                Application Implicit function argument ->
                    if prettyShowImplicits config
                        then
                            let functionText = prettyWithConfig config (precLevel ApplicationPrecedence) function
                                argumentText = prettyWithConfig config 0 argument
                                rendered = functionText <> " {" <> argumentText <> "}"
                             in parenthesizeIf (currentPrecedence > precLevel ApplicationPrecedence) rendered
                        else prettyWithConfig config currentPrecedence function
                Pi Explicit (Identifier "_") domain codomain ->
                    let domainText = prettyWithConfig config (precLevel ApplicationPrecedence) domain
                        codomainText = prettyWithConfig config (precLevel ArrowPrecedence) codomain
                        rendered = domainText <> " -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > precLevel ArrowPrecedence) rendered
                Pi Explicit parameter domain codomain ->
                    let domainText = prettyWithConfig config 0 domain
                        codomainText = prettyWithConfig config (precLevel ArrowPrecedence) codomain
                        rendered = "(" <> prettyIdentifier parameter <> " : " <> domainText <> ") -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > precLevel ArrowPrecedence) rendered
                Pi Implicit parameter domain codomain ->
                    let domainText = prettyWithConfig config 0 domain
                        codomainText = prettyWithConfig config (precLevel ArrowPrecedence) codomain
                        rendered = "{" <> prettyIdentifier parameter <> " : " <> domainText <> "} -> " <> codomainText
                     in parenthesizeIf (currentPrecedence > precLevel ArrowPrecedence) rendered
                Let param Nothing defExpr body ->
                    let defText = prettyWithConfig config 0 defExpr
                        bodyText = prettyWithConfig config 0 body
                        rendered = "let " <> prettyIdentifier param <> " = " <> defText <> " in " <> bodyText
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered
                Let param (Just paramType) defExpr body ->
                    let typeText = prettyWithConfig config 0 paramType
                        defText = prettyWithConfig config 0 defExpr
                        bodyText = prettyWithConfig config 0 body
                        rendered = "let " <> prettyIdentifier param <> " : " <> typeText <> " = " <> defText <> " in " <> bodyText
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered
                Case target mMotive branches ->
                    let targetText = prettyWithConfig config 0 target
                        motiveText = case mMotive of
                            Just (mv, mt) -> " as " <> prettyIdentifier mv <> " return " <> prettyWithConfig config 0 mt
                            Nothing -> ""
                        formatBranch (CaseBranch con vars body) =
                            let headStr = Text.unwords (prettyIdentifier con : map prettyIdentifier vars)
                             in headStr <> " -> " <> prettyWithConfig config 0 body
                        branchesText = Text.intercalate " ; " (map formatBranch branches)
                        rendered = "case " <> targetText <> motiveText <> " of { " <> branchesText <> " }"
                     in parenthesizeIf (currentPrecedence > precLevel LambdaPrecedence) rendered

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

-- | Render an infix application `left op right` respecting operator fixity.
prettyInfixApp ::
    PrettyConfig ->
    FixityEnv ->
    Identifier ->
    Expression ->
    Expression ->
    Int ->
    Text
prettyInfixApp config env op left right currentPrecedence =
    let f = fixityOf env op
        p = fixityPrec f
        myAssoc = fixityAssoc f
        (Identifier opName) = op
        rendered =
            infixLeft config env p myAssoc left
                <> " "
                <> opName
                <> " "
                <> infixRight config env p myAssoc right
     in parenthesizeIf (currentPrecedence > p) rendered

infixLeft ::
    PrettyConfig ->
    FixityEnv ->
    Int ->
    Associativity ->
    Expression ->
    Text
infixLeft config env p myAssoc sub =
    case stripLoc sub of
        Application Explicit (Application Explicit (Variable op2) x) y ->
            let f2 = fixityOf env op2
                t = prettyInfixApp config env op2 x y p
             in if parenLeft p myAssoc f2
                    then "(" <> t <> ")"
                    else t
        _ -> prettyWithConfig config p sub

infixRight ::
    PrettyConfig ->
    FixityEnv ->
    Int ->
    Associativity ->
    Expression ->
    Text
infixRight config env p myAssoc sub =
    case stripLoc sub of
        Application Explicit (Application Explicit (Variable op2) x) y ->
            let f2 = fixityOf env op2
                t = prettyInfixApp config env op2 x y p
             in if parenRight p myAssoc f2
                    then "(" <> t <> ")"
                    else t
        _ -> prettyWithConfig config p sub

-- | Does the left operand of an infix operator (precedence `p`, associativity
-- `myAssoc`) need parentheses when it is itself an infix application with fixity `f2`?
parenLeft :: Int -> Associativity -> Fixity -> Bool
parenLeft p myAssoc (Fixity { fixityPrec = p2, fixityAssoc = a2 })
    | p2 < p = True
    | p2 == p = not (myAssoc == AssocLeft && a2 == AssocLeft)
    | otherwise = False

-- | Does the right operand of an infix operator need parentheses?
parenRight :: Int -> Associativity -> Fixity -> Bool
parenRight p myAssoc (Fixity { fixityPrec = p2, fixityAssoc = a2 })
    | p2 < p = True
    | p2 == p = not (myAssoc == AssocRight && a2 == AssocRight)
    | otherwise = False

stripLoc :: Expression -> Expression
stripLoc (Located _ e) = stripLoc e
stripLoc e = e
