{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( parseExpression
  , parseStatement
  ) where

import AST (Expression (..), Identifier (..), Statement (..))
import qualified Lexer
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec

type Parser = Parsec Void Text

parseVariable :: Parser Expression
parseVariable = Variable <$> Lexer.identifier

parseUniverse :: Parser Expression
parseUniverse = Universe <$ Lexer.reservedKeyword "Type"

parseIdentity :: Parser Expression
parseIdentity = Identity <$ Lexer.reservedKeyword "Id"

parseReflexivity :: Parser Expression
parseReflexivity = Reflexivity <$ Lexer.reservedKeyword "refl"

parseJ :: Parser Expression
parseJ = J <$ Lexer.reservedKeyword "J"

parseAtomicExpression :: Parser Expression
parseAtomicExpression =
  parseUniverse
    <|> parseIdentity
    <|> parseReflexivity
    <|> parseJ
    <|> parseVariable
    <|> Lexer.parentheses expressionParser

parseApplication :: Parser Expression
parseApplication = do
  headExpression <- parseAtomicExpression
  argumentExpressions <- many parseAtomicExpression
  pure (foldl Application headExpression argumentExpressions)

parseDependentBinder :: Parser (Identifier, Expression)
parseDependentBinder = Lexer.parentheses $ do
  parameterName <- Lexer.identifier
  _ <- Lexer.symbol ":"
  parameterType <- expressionParser
  pure (parameterName, parameterType)

parseArrowOrApplication :: Parser Expression
parseArrowOrApplication = parseDependentArrow <|> parseNonDependentArrow
  where
    parseDependentArrow = do
      (parameterName, parameterType) <- try $ do
        binder <- parseDependentBinder
        _ <- Lexer.symbol "->"
        pure binder
      returnType <- expressionParser
      pure (Pi parameterName parameterType returnType)

    parseNonDependentArrow = do
      domainType <- parseApplication
      (do
         _ <- Lexer.symbol "->"
         codomainType <- expressionParser
         pure (Pi (Identifier "_") domainType codomainType)
       ) <|> pure domainType

parseAnnotation :: Parser Expression
parseAnnotation = do
  termExpression <- parseArrowOrApplication
  (do
     _ <- Lexer.symbol ":"
     typeExpression <- expressionParser
     pure (Annotation termExpression typeExpression)
   ) <|> pure termExpression

parseLambdaParameter :: Parser (Identifier, Maybe Expression)
parseLambdaParameter =
  try (Lexer.parentheses $ do
    parameterName <- Lexer.identifier
    _ <- Lexer.symbol ":"
    parameterType <- expressionParser
    pure (parameterName, Just parameterType))
  <|> ((\name -> (name, Nothing)) <$> Lexer.identifier)

parseLambda :: Parser Expression
parseLambda = do
  _ <- Lexer.symbol "\\"
  (parameterName, maybeParameterType) <- parseLambdaParameter
  _ <- Lexer.symbol "->"
  body <- expressionParser
  pure (Lambda parameterName maybeParameterType body)

expressionParser :: Parser Expression
expressionParser = parseLambda <|> parseAnnotation

parseDefinition :: Parser Statement
parseDefinition = do
  _ <- Lexer.reservedKeyword "def"
  name <- Lexer.identifier
  _ <- Lexer.symbol ":"
  declaredType <- expressionParser
  _ <- Lexer.symbol "="
  bodyTerm <- expressionParser
  pure (Definition name declaredType bodyTerm)

parseEvaluation :: Parser Statement
parseEvaluation = Evaluation <$> expressionParser

statementParser :: Parser Statement
statementParser = parseDefinition <|> parseEvaluation

parseExpression :: Text -> Either (ParseErrorBundle Text Void) Expression
parseExpression = parse (Lexer.spaceConsumer *> expressionParser <* eof) "<input>"

parseStatement :: Text -> Either (ParseErrorBundle Text Void) Statement
parseStatement = parse (Lexer.spaceConsumer *> statementParser <* eof) "<input>"
