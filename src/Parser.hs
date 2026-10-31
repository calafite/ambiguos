{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( parseExpression
  ) where

import AST (Expression (..), Identifier)
import qualified Lexer
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec

type Parser = Parsec Void Text

parseVariable :: Parser Expression
parseVariable = Variable <$> Lexer.identifier

parseUniverse :: Parser Expression
parseUniverse = Universe <$ Lexer.reservedKeyword "Type"

parseLambda :: Parser Expression
parseLambda = do
  _ <- Lexer.symbol "\\"
  parameterName <- Lexer.identifier
  _ <- Lexer.symbol "->"
  body <- expressionParser
  pure (Lambda parameterName body)

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

expressionParser :: Parser Expression
expressionParser = parseLambda <|> parseApplication

parseExpression :: Text -> Either (ParseErrorBundle Text Void) Expression
parseExpression = parse (Lexer.spaceConsumer *> expressionParser <* eof) "<input>"
