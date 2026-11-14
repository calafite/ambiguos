{-# LANGUAGE OverloadedStrings #-}

module Lexer (
    SourcePos (..),
    PosToken (..),
    Token (..),
    LexError (..),
    tokenize,
    renderLexError,
    prettyToken,
    initialPos,
    advancePosChar,
    advancePosString,
) where

import AST (Identifier (..))
import Automata.DFA (compileNFAToDFA, matchPrefixDFA)
import Automata.NFA (compileRegexToNFA)
import Automata.Types (DFA, Regex (..), literalString, matchAny)
import Data.Char (isAlphaNum, isSpace)
import Data.Text (Text)
import qualified Data.Text as Text
import Diagnostics (SourcePos (..))

initialPos :: SourcePos
initialPos = SourcePos 1 1

advancePosChar :: SourcePos -> Char -> SourcePos
advancePosChar (SourcePos l _) '\n' = SourcePos (l + 1) 1
advancePosChar (SourcePos l c) '\t' = SourcePos l (c + 4)
advancePosChar (SourcePos l c) _ = SourcePos l (c + 1)

advancePosString :: SourcePos -> String -> SourcePos
advancePosString = foldl advancePosChar

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
    | TokenKeywordInfixL
    | TokenKeywordInfixR
    | TokenKeywordInfix
    | TokenKeywordAs
    | TokenKeywordReturn
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
    | TokenOperator Identifier
    | TokenIdentifier Identifier
    deriving (Eq, Ord, Show)

data PosToken = PosToken
    { tokenPos :: !SourcePos
    , tokenValue :: !Token
    }
    deriving (Eq, Ord, Show)

data LexError
    = UnexpectedCharacter !SourcePos !Char
    | UnterminatedBlockComment !SourcePos
    deriving (Eq, Show)

prettyToken :: Token -> Text
prettyToken tok = case tok of
    TokenKeywordType -> "'Type'"
    TokenKeywordDef -> "'def'"
    TokenKeywordData -> "'data'"
    TokenKeywordWhere -> "'where'"
    TokenKeywordCase -> "'case'"
    TokenKeywordOf -> "'of'"
    TokenKeywordLet -> "'let'"
    TokenKeywordIn -> "'in'"
    TokenKeywordId -> "'Id'"
    TokenKeywordRefl -> "'refl'"
    TokenKeywordJ -> "'J'"
    TokenKeywordVoid -> "'Void'"
    TokenKeywordAbort -> "'abort'"
    TokenKeywordNat -> "'Nat'"
    TokenKeywordZero -> "'zero'"
    TokenKeywordSucc -> "'successor'"
    TokenKeywordNatRec -> "'natRec'"
    TokenKeywordInfixL -> "'infixl'"
    TokenKeywordInfixR -> "'infixr'"
    TokenKeywordInfix  -> "'infix'"
    TokenKeywordAs     -> "'as'"
    TokenKeywordReturn -> "'return'"
    TokenNatural n -> Text.pack (show n)
    TokenBackslash -> "'\\'"
    TokenArrow -> "'->'"
    TokenColon -> "':'"
    TokenEquals -> "'='"
    TokenPipe -> "'|'"
    TokenSemicolon -> "';'"
    TokenLeftParen -> "'('"
    TokenRightParen -> "')'"
    TokenLeftBracket -> "'['"
    TokenRightBracket -> "']'"
    TokenLeftBrace -> "'{'"
    TokenRightBrace -> "'}'"
    TokenComma -> "','"
    TokenHole Nothing -> "'_'"
    TokenHole (Just (Identifier name)) -> "'?" <> name <> "'"
    TokenOperator (Identifier op) -> "'" <> op <> "'"
    TokenIdentifier (Identifier ident) -> "'" <> ident <> "'"

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

opSymbols :: [Char]
opSymbols = "+-*/<>=!&|$%^~."

tokenize :: Text -> Either LexError [PosToken]
tokenize sourceText = scanLoop initialPos (Text.unpack sourceText)
  where
    scanLoop _ [] = Right []
    scanLoop pos remaining@(headChar : rest)
        | isSpace headChar =
            scanLoop (advancePosChar pos headChar) rest
        | take 2 remaining == "--" =
            let (comment, restAfter) = span (/= '\n') remaining
                pos' = advancePosString pos comment
             in scanLoop pos' restAfter
        | take 2 remaining == "{-" =
            case skipBlockComment (advancePosString pos "{-") (1 :: Int) (drop 2 remaining) of
                Left err -> Left err
                Right (pos', afterBlock) -> scanLoop pos' afterBlock
        | Just (arrowStr, restAfter) <- matchPrefixDFA dfaArrow remaining =
            let pos' = advancePosString pos arrowStr
             in (PosToken pos TokenArrow :) <$> scanLoop pos' restAfter
        | Just (numStr, restAfter) <- matchPrefixDFA dfaNatural remaining =
            let n = read numStr :: Integer
                pos' = advancePosString pos numStr
             in (PosToken pos (TokenNatural n) :) <$> scanLoop pos' restAfter
        | headChar == '?' =
            let (identChars, restAfter) = span (\c -> isAlphaNum c || c == '_') rest
                mIdent = if null identChars then Nothing else Just (Identifier (Text.pack identChars))
                consumed = headChar : identChars
                pos' = advancePosString pos consumed
             in (PosToken pos (TokenHole mIdent) :) <$> scanLoop pos' restAfter
        | Just (identStr, restAfter) <- matchPrefixDFA dfaIdentifier remaining =
            let token = classifyIdentifier (Text.pack identStr)
                pos' = advancePosString pos identStr
             in (PosToken pos token :) <$> scanLoop pos' restAfter
        | headChar `elem` opSymbols =
            let (opStr, restAfter) = span (`elem` opSymbols) remaining
                pos' = advancePosString pos opStr
                token = case opStr of
                    "=" -> TokenEquals
                    "|" -> TokenPipe
                    _ -> TokenOperator (Identifier (Text.pack opStr))
             in (PosToken pos token :) <$> scanLoop pos' restAfter
        | otherwise =
            case headChar of
                '\\' -> (PosToken pos TokenBackslash :) <$> scanLoop (advancePosChar pos headChar) rest
                ':' -> (PosToken pos TokenColon :) <$> scanLoop (advancePosChar pos headChar) rest
                ';' -> (PosToken pos TokenSemicolon :) <$> scanLoop (advancePosChar pos headChar) rest
                '(' -> (PosToken pos TokenLeftParen :) <$> scanLoop (advancePosChar pos headChar) rest
                ')' -> (PosToken pos TokenRightParen :) <$> scanLoop (advancePosChar pos headChar) rest
                '[' -> (PosToken pos TokenLeftBracket :) <$> scanLoop (advancePosChar pos headChar) rest
                ']' -> (PosToken pos TokenRightBracket :) <$> scanLoop (advancePosChar pos headChar) rest
                '{' -> (PosToken pos TokenLeftBrace :) <$> scanLoop (advancePosChar pos headChar) rest
                '}' -> (PosToken pos TokenRightBrace :) <$> scanLoop (advancePosChar pos headChar) rest
                ',' -> (PosToken pos TokenComma :) <$> scanLoop (advancePosChar pos headChar) rest
                c -> Left (UnexpectedCharacter pos c)

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
        "infixl" -> TokenKeywordInfixL
        "infixr" -> TokenKeywordInfixR
        "infix"  -> TokenKeywordInfix
        "as"     -> TokenKeywordAs
        "return" -> TokenKeywordReturn
        "_" -> TokenHole Nothing
        _
            | Text.isPrefixOf "_" text ->
                TokenHole (Just (Identifier (Text.drop 1 text)))
            | otherwise ->
                TokenIdentifier (Identifier text)

    skipBlockComment pos 0 text = Right (pos, text)
    skipBlockComment pos _ [] = Left (UnterminatedBlockComment pos)
    skipBlockComment pos depth ('{' : '-' : rest) =
        skipBlockComment (advancePosString pos "{-") (depth + 1) rest
    skipBlockComment pos depth ('-' : '}' : rest) =
        skipBlockComment (advancePosString pos "-}") (depth - 1) rest
    skipBlockComment pos depth (c : rest) =
        skipBlockComment (advancePosChar pos c) depth rest

renderLexError :: LexError -> Text
renderLexError err = case err of
    UnexpectedCharacter pos c ->
        "Lexical error at line "
            <> Text.pack (show (posLine pos))
            <> ", col "
            <> Text.pack (show (posColumn pos))
            <> ": Unexpected character '"
            <> Text.singleton c
            <> "'"
    UnterminatedBlockComment pos ->
        "Lexical error at line "
            <> Text.pack (show (posLine pos))
            <> ", col "
            <> Text.pack (show (posColumn pos))
            <> ": Unterminated block comment '{- ... -}'"
