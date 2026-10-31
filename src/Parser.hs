{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( parseExpression
  ) where

import AST (Expression (..), Identifier (..))
import qualified Lexer
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec

type Parser = Parsec Void Text

parseVariable :: Parser Expression
parseVariable = Variable <$> Lexer.identifier

parseUniverse :: Parser Expression
parseUniverse = Universe <$ Lexer.reservedKeyword "Type"

parseAtomicExpression :: Parser Expression
parseAtomicExpression =
  parseUniverse
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

parseLambda :: Parser Expression
parseLambda = do
  _ <- Lexer.symbol "\\"
  parameterName <- Lexer.identifier
  _ <- Lexer.symbol "->"
  body <- expressionParser
  pure (Lambda parameterName body)

expressionParser :: Parser Expression
expressionParser = parseLambda <|> parseAnnotation

parseExpression :: Text -> Either (ParseErrorBundle Text Void) Expression
parseExpression = parse (Lexer.spaceConsumer *> expressionParser <* eof) "<input>"
