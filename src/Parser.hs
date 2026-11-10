{-# LANGUAGE OverloadedStrings #-}

module Parser (
    ParseError (..),
    parseExpression,
    parseStatement,
    parseProgram,
    renderParseError,
) where

import AST (Expression (..), Identifier (..), Statement (..), Visibility (..))
import Control.Applicative (Alternative (..), optional)
import Data.Text (Text)
import qualified Data.Text as Text
import Lexer (LexError, Token (..), renderLexError, tokenize)

data ParseError
    = ErrorLexical LexError
    | UnexpectedEndOfInput
    | ExpectedToken Text Token
    | UnexpectedToken Token
    deriving (Eq, Show)

newtype Parser a = Parser
    { runParser :: [Token] -> Either ParseError (a, [Token])
    }

instance Functor Parser where
    fmap f (Parser p) = Parser $ \tokens -> do
        (res, remaining) <- p tokens
        pure (f res, remaining)

instance Applicative Parser where
    pure val = Parser $ \tokens -> Right (val, tokens)
    Parser pf <*> Parser pa = Parser $ \tokens -> do
        (f, afterF) <- pf tokens
        (a, afterA) <- pa afterF
        pure (f a, afterA)

instance Alternative Parser where
  empty = Parser $ \_ -> Left UnexpectedEndOfInput
  Parser p1 <|> Parser p2 = Parser $ \tokens ->
    case p1 tokens of
      Right result -> Right result
      Left _       -> p2 tokens

instance Monad Parser where
  Parser p >>= f = Parser $ \tokens -> do
    (val, remaining) <- p tokens
    runParser (f val) remaining

peekToken :: Parser (Maybe Token)
peekToken = Parser $ \tokens -> case tokens of
    []      -> Right (Nothing, [])
    (t : _) -> Right (Just t, tokens)

consumeToken :: Parser Token
consumeToken = Parser $ \tokens -> case tokens of
    []       -> Left UnexpectedEndOfInput
    (t : ts) -> Right (t, ts)

expectToken :: Token -> Text -> Parser ()
expectToken expected description = do
    t <- consumeToken
    if t == expected
        then pure ()
        else Parser $ \_ -> Left (ExpectedToken description t)

parseIdentifier :: Parser Identifier
parseIdentifier = do
    t <- consumeToken
    case t of
        TokenIdentifier ident -> pure ident
        other -> Parser $ \_ -> Left (ExpectedToken "identifier" other)

desugarNatural :: Integer -> Expression
desugarNatural n
    | n <= 0    = Zero
    | otherwise = Application Explicit Succ (desugarNatural (n - 1))

desugarList :: [Expression] -> Expression
desugarList [] = Application Explicit (Variable (Identifier "nil")) (Hole Nothing)
desugarList (x : xs) =
    Application Explicit
        (Application Explicit
            (Application Explicit (Variable (Identifier "cons")) (Hole Nothing))
            x)
        (desugarList xs)

parseListElements :: Parser [Expression]
parseListElements = do
    firstElem <- expressionParser
    restElems <- many (expectToken TokenComma "','" *> expressionParser)
    pure (firstElem : restElems)

parseListLiteral :: Parser Expression
parseListLiteral = do
    _ <- consumeToken
    nextToken <- peekToken
    case nextToken of
        Just TokenRightBracket -> do
            _ <- consumeToken
            pure (desugarList [])
        _ -> do
            elems <- parseListElements
            expectToken TokenRightBracket "']'"
            pure (desugarList elems)

parseAtomicExpression :: Parser Expression
parseAtomicExpression = do
    nextToken <- peekToken
    case nextToken of
        Just TokenKeywordType   -> Universe <$ consumeToken
        Just TokenKeywordId     -> Identity <$ consumeToken
        Just TokenKeywordRefl   -> Reflexivity <$ consumeToken
        Just TokenKeywordJ      -> J <$ consumeToken
        Just TokenKeywordVoid   -> VoidType <$ consumeToken
        Just TokenKeywordAbort  -> Abort <$ consumeToken
        Just TokenKeywordNat    -> NatType <$ consumeToken
        Just TokenKeywordZero   -> Zero <$ consumeToken
        Just TokenKeywordSucc   -> Succ <$ consumeToken
        Just TokenKeywordNatRec -> NatRec <$ consumeToken
        Just (TokenNatural n)   -> desugarNatural n <$ consumeToken

        Just (TokenIdentifier (Identifier "_")) ->
            Hole Nothing <$ consumeToken

        Just (TokenIdentifier ident) ->
            Variable ident <$ consumeToken

        Just TokenLeftBracket ->
            parseListLiteral

        Just TokenLeftParen -> do
            _ <- consumeToken
            expr <- expressionParser
            expectToken TokenRightParen "')'"
            pure expr

        Just other -> Parser $ \_ -> Left (UnexpectedToken other)
        Nothing    -> Parser $ \_ -> Left UnexpectedEndOfInput

-- | Parses an application argument: either explicit `atom` or explicit override `{expr}`
parseAppArgument :: Parser (Visibility, Expression)
parseAppArgument = parseImplicitOverride <|> parseExplicitArg
  where
    parseImplicitOverride = do
        expectToken TokenLeftBrace "'{'"
        expr <- expressionParser
        expectToken TokenRightBrace "'}'"
        pure (Implicit, expr)
    parseExplicitArg = do
        expr <- parseAtomicExpression
        pure (Explicit, expr)

parseApplication :: Parser Expression
parseApplication = do
    headExpr <- parseAtomicExpression
    argExprs <- many parseAppArgument
    pure (foldl (\acc (vis, arg) -> Application vis acc arg) headExpr argExprs)

-- | Parses dependent arrows: (x y : A) -> B or {A B : Type} -> C
parseDependentArrow :: Parser Expression
parseDependentArrow = parseExplicit <|> parseImplicit
  where
    parseExplicit = do
        expectToken TokenLeftParen "'('"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser
        expectToken TokenRightParen "')'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser
        pure (foldr (\name acc -> Pi Explicit name domainType acc) codomainType parameterNames)

    parseImplicit = do
        expectToken TokenLeftBrace "'{'"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser
        expectToken TokenRightBrace "'}'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser
        pure (foldr (\name acc -> Pi Implicit name domainType acc) codomainType parameterNames)

parseNonDependentArrow :: Parser Expression
parseNonDependentArrow = do
    domain <- parseApplication
    isArrow <- (True <$ expectToken TokenArrow "'->'") <|> pure False
    if isArrow
        then do
            codomain <- expressionParser
            pure (Pi Explicit (Identifier "_") domain codomain)
        else pure domain

parseArrowOrApplication :: Parser Expression
parseArrowOrApplication = parseDependentArrow <|> parseNonDependentArrow

parseAnnotation :: Parser Expression
parseAnnotation = do
    termExpr <- parseArrowOrApplication
    isAnnotated <- (True <$ expectToken TokenColon "':'") <|> pure False
    if isAnnotated
        then do
            annType <- expressionParser
            pure (Annotation termExpr annType)
        else pure termExpr

data ParameterGroup
    = SimpleParameters [Identifier]
    | TypedParameters Visibility [Identifier] Expression

parseParameterGroup :: Parser ParameterGroup
parseParameterGroup = parseTypedParen <|> parseTypedBrace <|> parseSimple
  where
    parseTypedParen = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser
        expectToken TokenRightParen "')'"
        pure (TypedParameters Explicit names paramType)

    parseTypedBrace = do
        expectToken TokenLeftBrace "'{'"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser
        expectToken TokenRightBrace "'}'"
        pure (TypedParameters Implicit names paramType)

    parseSimple = do
        names <- some parseIdentifier
        pure (SimpleParameters names)

parseLambda :: Parser Expression
parseLambda = do
    expectToken TokenBackslash "'\\'"
    paramGroups <- some parseParameterGroup
    expectToken TokenArrow "'->'"
    body <- expressionParser
    pure (foldr expandGroup body paramGroups)
  where
    expandGroup (SimpleParameters names) acc =
        foldr (\name inner -> Lambda Explicit name Nothing inner) acc names
    expandGroup (TypedParameters vis names pType) acc =
        foldr (\name inner -> Lambda vis name (Just pType) inner) acc names

expressionParser :: Parser Expression
expressionParser = parseLambda <|> parseAnnotation

parseDefinition :: Parser Statement
parseDefinition = do
    expectToken TokenKeywordDef "'def'"
    name <- parseIdentifier
    maybeType <- optional (expectToken TokenColon "':'" *> expressionParser)
    expectToken TokenEquals "'='"
    bodyTerm <- expressionParser
    pure (Definition name maybeType bodyTerm)

parseEvaluation :: Parser Statement
parseEvaluation = Evaluation <$> expressionParser

statementParser :: Parser Statement
statementParser = parseDefinition <|> parseEvaluation

runCompleteParser :: Parser a -> [Token] -> Either ParseError a
runCompleteParser parser tokens =
    case runParser parser tokens of
        Right (result, []) -> Right result
        Right (_, unconsumed : _) -> Left (UnexpectedToken unconsumed)
        Left err -> Left err

parseExpression :: Text -> Either ParseError Expression
parseExpression input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks  -> Right toks
    runCompleteParser expressionParser tokens

parseStatement :: Text -> Either ParseError Statement
parseStatement input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks  -> Right toks
    runCompleteParser statementParser tokens

parseProgram :: Text -> Either ParseError [Statement]
parseProgram input = do
  tokens <- case tokenize input of
    Left lexErr -> Left (ErrorLexical lexErr)
    Right toks  -> Right toks
  runCompleteParser (many statementParser) tokens

renderParseError :: ParseError -> Text
renderParseError err = case err of
    ErrorLexical lexErr -> renderLexError lexErr
    UnexpectedEndOfInput -> "Syntax error: Unexpected end of input."
    ExpectedToken expected found ->
        "Syntax error: Expected " <> expected <> ", but found: " <> Text.pack (show found)
    UnexpectedToken token ->
        "Syntax error: Unexpected token: " <> Text.pack (show token)
