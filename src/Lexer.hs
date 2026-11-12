{-# LANGUAGE OverloadedStrings #-}

module Lexer (
    Token (..),
    LexError (..),
    tokenize,
    renderLexError,
) where

import AST (Identifier (..))
import Automata.DFA (compileNFAToDFA, matchPrefixDFA)
import Automata.NFA (compileRegexToNFA)
import Automata.Types (DFA, Regex (..), literalString, matchAny)
import Data.Char (isAlphaNum, isSpace)
import Data.Text (Text)
import qualified Data.Text as Text

data Token
    = TokenKeywordType
    | TokenKeywordDef
    | TokenKeywordData
    | TokenKeywordWhere
    | TokenKeywordCase
    | TokenKeywordOf
    | TokenKeywordLet
    | TokenKeywordIn
    | TokenKeywordId
    | TokenKeywordRefl
    | TokenKeywordJ
    | TokenKeywordVoid
    | TokenKeywordAbort
    | TokenKeywordNat
    | TokenKeywordZero
    | TokenKeywordSucc
    | TokenKeywordNatRec
    | TokenNatural Integer
    | TokenBackslash
    | TokenArrow
    | TokenColon
    | TokenEquals
    | TokenPipe
    | TokenSemicolon
    | TokenLeftParen
    | TokenRightParen
    | TokenLeftBracket
    | TokenRightBracket
    | TokenLeftBrace
    | TokenRightBrace
    | TokenComma
    | TokenHole (Maybe Identifier)
    | TokenIdentifier Identifier
    deriving (Eq, Ord, Show)

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

dfaNatural :: DFA
dfaNatural = compileNFAToDFA (compileRegexToNFA regex)
  where
    digitChars = ['0' .. '9']
    digits = matchAny digitChars
    regex = Concat digits (Star digits)

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
        | Just (numStr, rest) <- matchPrefixDFA dfaNatural remaining =
            let n = read numStr :: Integer
             in (TokenNatural n :) <$> scanLoop (dropWhile isSpace rest)
        | (headChar : rest) <- remaining
        , headChar == '?' =
            let (identChars, restAfter) = span (\c -> isAlphaNum c || c == '_') rest
                mIdent = if null identChars then Nothing else Just (Identifier (Text.pack identChars))
             in (TokenHole mIdent :) <$> scanLoop (dropWhile isSpace restAfter)
        | Just (identStr, rest) <- matchPrefixDFA dfaIdentifier remaining =
            let token = classifyIdentifier (Text.pack identStr)
             in (token :) <$> scanLoop (dropWhile isSpace rest)
        | (headChar : rest) <- remaining =
            case headChar of
                '\\' -> (TokenBackslash :) <$> scanLoop (dropWhile isSpace rest)
                ':' -> (TokenColon :) <$> scanLoop (dropWhile isSpace rest)
                '=' -> (TokenEquals :) <$> scanLoop (dropWhile isSpace rest)
                '|' -> (TokenPipe :) <$> scanLoop (dropWhile isSpace rest)
                ';' -> (TokenSemicolon :) <$> scanLoop (dropWhile isSpace rest)
                '(' -> (TokenLeftParen :) <$> scanLoop (dropWhile isSpace rest)
                ')' -> (TokenRightParen :) <$> scanLoop (dropWhile isSpace rest)
                '[' -> (TokenLeftBracket :) <$> scanLoop (dropWhile isSpace rest)
                ']' -> (TokenRightBracket :) <$> scanLoop (dropWhile isSpace rest)
                '{' -> (TokenLeftBrace :) <$> scanLoop (dropWhile isSpace rest)
                '}' -> (TokenRightBrace :) <$> scanLoop (dropWhile isSpace rest)
                ',' -> (TokenComma :) <$> scanLoop (dropWhile isSpace rest)
                c
                    | isSpace c -> scanLoop (dropWhile isSpace rest)
                    | otherwise -> Left (UnexpectedCharacter c)
        | otherwise = Right []

    classifyIdentifier text = case text of
        "Type" -> TokenKeywordType
        "def" -> TokenKeywordDef
        "data" -> TokenKeywordData
        "where" -> TokenKeywordWhere
        "case" -> TokenKeywordCase
        "of" -> TokenKeywordOf
        "let" -> TokenKeywordLet
        "in" -> TokenKeywordIn
        "Id" -> TokenKeywordId
        "refl" -> TokenKeywordRefl
        "J" -> TokenKeywordJ
        "Void" -> TokenKeywordVoid
        "abort" -> TokenKeywordAbort
        "Nat" -> TokenKeywordNat
        "zero" -> TokenKeywordZero
        "successor" -> TokenKeywordSucc
        "succ" -> TokenKeywordSucc
        "natRec" -> TokenKeywordNatRec
        "_" -> TokenHole Nothing
        _
            | Text.isPrefixOf "_" text ->
                TokenHole (Just (Identifier (Text.drop 1 text)))
            | otherwise ->
                TokenIdentifier (Identifier text)

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
