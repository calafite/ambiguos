{-# LANGUAGE OverloadedStrings #-}

module Lexer
  ( Token (..)
  , LexError (..)
  , tokenize
  , renderLexError{-# LANGUAGE OverloadedStrings #-}

  module Lexer
    ( Token (..)
    , LexError (..)
    , tokenize
    , renderLexError
    ) where

  import AST (Identifier (..))
  import Automata.DFA (DFA, compileNFAToDFA, matchPrefixDFA)
  import Automata.NFA (compileRegexToNFA)
  import Automata.Types (Regex (..), literalString, matchAny)
  import Data.Char (isSpace)
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

  dfaIdentifier :: DFA
  dfaIdentifier = compileNFAToDFA (compileRegexToNFA regex)
    where
      alphaChars = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['_']
      digitChars = ['0' .. '9']
      startPattern = matchAny alphaChars
      restPattern = matchAny (alphaChars ++ digitChars)
      regex = Concat startPattern (Star restPattern)

  dfaArrow :: DFA
  dfaArrow = compileNFAToDFA (compileRegexToNFA (literalString "->"))

  tokenize :: Text -> Either LexError [Token]
  tokenize sourceText = scanLoop (Text.unpack (Text.stripStart sourceText))
    where
      scanLoop remaining
        | null remaining = Right []
        | take 2 remaining == "--" =
            let afterComment = dropWhile (/= '\n') remaining
            in scanLoop (dropWhile isSpace afterComment)
        | take 2 remaining == "{-" =
            case skipBlockComment 1 (drop 2 remaining) of
              Left err -> Left err
              Right afterBlock -> scanLoop (dropWhile isSpace afterBlock)
        | Just (_, rest) <- matchPrefixDFA dfaArrow remaining =
            (TokenArrow :) <$> scanLoop (dropWhile isSpace rest)
        | Just (identStr, rest) <- matchPrefixDFA dfaIdentifier remaining =
            let token = classifyIdentifier (Text.pack identStr)
            in (token :) <$> scanLoop (dropWhile isSpace rest)
        | otherwise =
            let headChar = head remaining
                rest = tail remaining
            in case headChar of
                 '\\' -> (TokenBackslash :) <$> scanLoop (dropWhile isSpace rest)
                 ':'  -> (TokenColon :) <$> scanLoop (dropWhile isSpace rest)
                 '='  -> (TokenEquals :) <$> scanLoop (dropWhile isSpace rest)
                 '('  -> (TokenLeftParen :) <$> scanLoop (dropWhile isSpace rest)
                 ')'  -> (TokenRightParen :) <$> scanLoop (dropWhile isSpace rest)
                 c
                   | isSpace c -> scanLoop (dropWhile isSpace rest)
                   | otherwise -> Left (UnexpectedCharacter c)

      classifyIdentifier text = case text of
        "Type" -> TokenKeywordType
        "def"  -> TokenKeywordDef
        "Id"   -> TokenKeywordId
        "refl" -> TokenKeywordRefl
        "J"    -> TokenKeywordJ
        _      -> TokenIdentifier (Identifier text)

      skipBlockComment :: Int -> String -> Either LexError String
      skipBlockComment 0 text = Right text
      skipBlockComment _ [] = Left UnterminatedBlockComment
      skipBlockComment depth ('{' : '-' : rest) = skipBlockComment (depth + 1) rest
      skipBlockComment depth ('-' : '}' : rest) = skipBlockComment (depth - 1) rest
      skipBlockComment depth (_ : rest) = skipBlockComment depth rest

  renderLexError :: LexError -> Text
  renderLexError err = case err of
    UnexpectedCharacter c -> "Lexical error: Unexpected character '" <> Text.singleton c <> "'"
    UnterminatedBlockComment -> "Lexical error: Unterminated block comment '{- ... -}'"

  ) where

import AST (Identifier (..))
import Automata.DFA (compileNFAToDFA, matchPrefixDFA)
import Automata.NFA (compileRegexToNFA)
import Automata.Types (DFA, Regex (..), literalString, matchAny)
import Data.Char (isSpace)
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

-- | Formal regular expression for Identifiers: ([a-zA-Z_])([a-zA-Z0-9_])*
dfaIdentifier :: DFA
dfaIdentifier = compileNFAToDFA (compileRegexToNFA regex)
  where
    alphaChars = ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['_']
    digitChars = ['0' .. '9']
    startPattern = matchAny alphaChars
    restPattern = matchAny (alphaChars ++ digitChars)
    regex = Concat startPattern (Star restPattern)

-- | Formal regular expression for the Arrow symbol: '->'
dfaArrow :: DFA
dfaArrow = compileNFAToDFA (compileRegexToNFA (literalString "->"))

tokenize :: Text -> Either LexError [Token]
tokenize sourceText = scanLoop (Text.unpack (Text.stripStart sourceText))
  where
    scanLoop remaining
      | null remaining = Right []
      -- Skip single-line comments
      | take 2 remaining == "--" =
          let afterComment = dropWhile (/= '\n') remaining
          in scanLoop (dropWhile isSpace afterComment)
      -- Skip block comments
      | take 2 remaining == "{-" =
          case skipBlockComment 1 (drop 2 remaining) of
            Left err -> Left err
            Right afterBlock -> scanLoop (dropWhile isSpace afterBlock)
      -- Match arrows using the compiled DFA
      | Just (_, rest) <- matchPrefixDFA dfaArrow remaining =
          (TokenArrow :) <$> scanLoop (dropWhile isSpace rest)
      -- Match identifiers and keywords using the compiled DFA
      | Just (identStr, rest) <- matchPrefixDFA dfaIdentifier remaining =
          let token = classifyIdentifier (Text.pack identStr)
          in (token :) <$> scanLoop (dropWhile isSpace rest)
      -- Single-character punctuation tokens
      | otherwise =
          let headChar = head remaining
              rest = tail remaining
          in case headChar of
               '\\' -> (TokenBackslash :) <$> scanLoop (dropWhile isSpace rest)
               ':'  -> (TokenColon :) <$> scanLoop (dropWhile isSpace rest)
               '='  -> (TokenEquals :) <$> scanLoop (dropWhile isSpace rest)
               '('  -> (TokenLeftParen :) <$> scanLoop (dropWhile isSpace rest)
               ')'  -> (TokenRightParen :) <$> scanLoop (dropWhile isSpace rest)
               c
                 | isSpace c -> scanLoop (dropWhile isSpace rest)
                 | otherwise -> Left (UnexpectedCharacter c)

    classifyIdentifier text = case text of
      "Type" -> TokenKeywordType
      "def"  -> TokenKeywordDef
      "Id"   -> TokenKeywordId
      "refl" -> TokenKeywordRefl
      "J"    -> TokenKeywordJ
      _      -> TokenIdentifier (Identifier text)

    skipBlockComment :: Int -> String -> Either LexError String
    skipBlockComment 0 text = Right text
    skipBlockComment _ [] = Left UnterminatedBlockComment
    skipBlockComment depth ('{' : '-' : rest) = skipBlockComment (depth + 1) rest
    skipBlockComment depth ('-' : '}' : rest) = skipBlockComment (depth - 1) rest
    skipBlockComment depth (_ : rest) = skipBlockComment depth rest

renderLexError :: LexError -> Text
renderLexError err = case err of
  UnexpectedCharacter c -> "Lexical error: Unexpected character '" <> Text.singleton c <> "'"
  UnterminatedBlockComment -> "Lexical error: Unterminated block comment '{- ... -}'"
