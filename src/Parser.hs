{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( ParseError (..)
  , parseExpression
  , parseStatement
  , renderParseError
  ) where

import AST (Expression (..), Identifier (..), Statement (..))
import Control.Applicative (Alternative (..))
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
  []      -> Left UnexpectedEndOfInput
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

parseAtomicExpression :: Parser Expression
parseAtomicExpression = do
  nextToken <- peekToken
  case nextToken of
    Just TokenKeywordType -> consumeToken >> pure Universe
    Just TokenKeywordId   -> consumeToken >> pure Identity
    Just TokenKeywordRefl -> consumeToken >> pure Reflexivity
    Just TokenKeywordJ    -> consumeToken >> pure J
    Just (TokenIdentifier ident) -> consumeToken >> pure (Variable ident)
    Just TokenLeftParen -> do
      consumeToken
      expr <- expressionParser
      expectToken TokenRightParen "')'"
      pure expr
    Just other -> Parser $ \_ -> Left (UnexpectedToken other)
    Nothing    -> Parser $ \_ -> Left UnexpectedEndOfInput

parseApplication :: Parser Expression
parseApplication = do
  headExpr <- parseAtomicExpression
  argExprs <- many parseAtomicExpression
  pure (foldl Application headExpr argExprs)

parseDependentArrow :: Parser Expression
parseDependentArrow = do
  expectToken TokenLeftParen "'('"
  parameterName <- parseIdentifier
  expectToken TokenColon "':'"
  domainType <- expressionParser
  expectToken TokenRightParen "')'"
  expectToken TokenArrow "'->'"
  codomainType <- expressionParser
  pure (Pi parameterName domainType codomainType)

parseNonDependentArrow :: Parser Expression
parseNonDependentArrow = do
  domain <- parseApplication
  isArrow <- (True <$ expectToken TokenArrow "'->'") <|> pure False
  if isArrow
    then do
      codomain <- expressionParser
      pure (Pi (Identifier "_") domain codomain)
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

parseLambdaParameter :: Parser (Identifier, Maybe Expression)
parseLambdaParameter = parseAnnotatedParameter <|> parseSimpleParameter
  where
    parseAnnotatedParameter = do
      expectToken TokenLeftParen "'('"
      name <- parseIdentifier
      expectToken TokenColon "':'"
      paramType <- expressionParser
      expectToken TokenRightParen "')'"
      pure (name, Just paramType)

    parseSimpleParameter = do
      name <- parseIdentifier
      pure (name, Nothing)

parseLambda :: Parser Expression
parseLambda = do
  expectToken TokenBackslash "'\\'"
  (parameterName, maybeParamType) <- parseLambdaParameter
  expectToken TokenArrow "'->'"
  body <- expressionParser
  pure (Lambda parameterName maybeParamType body)

expressionParser :: Parser Expression
expressionParser = parseLambda <|> parseAnnotation

parseDefinition :: Parser Statement
parseDefinition = do
  expectToken TokenKeywordDef "'def'"
  name <- parseIdentifier
  expectToken TokenColon "':'"
  declaredType <- expressionParser
  expectToken TokenEquals "'='"
  bodyTerm <- expressionParser
  pure (Definition name declaredType bodyTerm)

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

renderParseError :: ParseError -> Text
renderParseError err = case err of
  ErrorLexical lexErr -> renderLexError lexErr
  UnexpectedEndOfInput -> "Syntax error: Unexpected end of input."
  ExpectedToken expected found ->
    "Syntax error: Expected " <> expected <> ", but found: " <> Text.pack (show found)
  UnexpectedToken token ->
    "Syntax error: Unexpected token: " <> Text.pack (show token)
