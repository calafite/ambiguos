{-# LANGUAGE OverloadedStrings #-}

module Lexer
  ( Token (..)
  , LexError (..)
  , tokenize
  , renderLexError
  ) where

import AST (Identifier (..))
import Data.Char (isAlpha, isAlphaNum, isSpace)
import Data.Text (Text)
import qualified Data.Text as Text

data Token
  = TokenKeywordType
  | TokenKeywordDef
  | TokenKeywordId
  | TokenKeywordRefl
  | TokenKeywordJ
  | TokenBackslash
  | TokenArrow
  | TokenColon
  | TokenEquals
  | TokenLeftParen
  | TokenRightParen
  | TokenIdentifier Identifier
  deriving (Eq, Show)

data LexError
  = UnexpectedCharacter Char
  | UnterminatedBlockComment
  deriving (Eq, Show)

tokenize :: Text -> Either LexError [Token]
tokenize = scanLoop . Text.stripStart
  where
    scanLoop remaining
      | Text.null remaining = Right []
      | Text.isPrefixOf "--" remaining =
          let afterComment = Text.dropWhile (/= '\n') remaining
          in scanLoop (Text.stripStart afterComment)
      | Text.isPrefixOf "{-" remaining =
          case skipBlockComment 1 (Text.drop 2 remaining) of
            Left err -> Left err
            Right afterBlock -> scanLoop (Text.stripStart afterBlock)
      | Text.isPrefixOf "->" remaining =
          (TokenArrow :) <$> scanLoop (Text.stripStart (Text.drop 2 remaining))
      | otherwise =
          let headChar = Text.head remaining
              tailText = Text.tail remaining
          in case headChar of
               '\\' -> (TokenBackslash :) <$> scanLoop (Text.stripStart tailText)
               ':'  -> (TokenColon :) <$> scanLoop (Text.stripStart tailText)
               '='  -> (TokenEquals :) <$> scanLoop (Text.stripStart tailText)
               '('  -> (TokenLeftParen :) <$> scanLoop (Text.stripStart tailText)
               ')'  -> (TokenRightParen :) <$> scanLoop (Text.stripStart tailText)
               c
                 | isIdentStart c ->
                     let (identText, rest) = Text.span isIdentPart remaining
                         token = classifyIdentifier identText
                     in (token :) <$> scanLoop (Text.stripStart rest)
                 | isSpace c ->
                     scanLoop (Text.stripStart tailText)
                 | otherwise ->
                     Left (UnexpectedCharacter c)

    isIdentStart c = isAlpha c || c == '_'
    isIdentPart c  = isAlphaNum c || c == '_'

    classifyIdentifier text = case text of
      "Type" -> TokenKeywordType
      "def"  -> TokenKeywordDef
      "Id"   -> TokenKeywordId
      "refl" -> TokenKeywordRefl
      "J"    -> TokenKeywordJ
      _      -> TokenIdentifier (Identifier text)

    skipBlockComment :: Int -> Text -> Either LexError Text
    skipBlockComment 0 text = Right text
    skipBlockComment depth text
      | Text.null text = Left UnterminatedBlockComment
      | Text.isPrefixOf "{-" text = skipBlockComment (depth + 1) (Text.drop 2 text)
      | Text.isPrefixOf "-}" text = skipBlockComment (depth - 1) (Text.drop 2 text)
      | otherwise = skipBlockComment depth (Text.tail text)

renderLexError :: LexError -> Text
renderLexError err = case err of
  UnexpectedCharacter c -> "Lexical error: Unexpected character '" <> Text.singleton c <> "'"
  UnterminatedBlockComment -> "Lexical error: Unterminated block comment '{- ... -}'"
