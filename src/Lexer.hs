{-# LANGUAGE OverloadedStrings #-}

module Lexer
  ( Parser
  , spaceConsumer
  , lexeme
  , symbol
  , parentheses
  , reservedKeyword
  , identifier
  ) where

import AST (Identifier (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as MegaparsecLexer

type Parser = Parsec Void Text

spaceConsumer :: Parser ()
spaceConsumer = MegaparsecLexer.space
  space1
  (MegaparsecLexer.skipLineComment "--")
  (MegaparsecLexer.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = MegaparsecLexer.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = MegaparsecLexer.symbol spaceConsumer

parentheses :: Parser a -> Parser a
parentheses = between (symbol "(") (symbol ")")

reservedKeywords :: [Text]
reservedKeywords = ["Type"]

reservedKeyword :: Text -> Parser ()
reservedKeyword keyword = lexeme . try $ do
  _ <- string keyword
  notFollowedBy (alphaNumChar <|> char '_')

identifier :: Parser Identifier
identifier = lexeme . try $ do
  firstCharacter <- letterChar <|> char '_'
  remainingCharacters <- many (alphaNumChar <|> char '_')
  let candidateName = Text.pack (firstCharacter : remainingCharacters)
  if candidateName `elem` reservedKeywords
    then fail ("Reserved keyword cannot be used as an identifier: " ++ Text.unpack candidateName)
    else pure (Identifier candidateName)
