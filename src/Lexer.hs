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
import Data.Char (chr, isAlphaNum, isDigit, isHexDigit, isSpace, digitToInt)
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
    | TokenDot
    | TokenKeywordModule
    | TokenKeywordImport
    | TokenKeywordQualified
    | TokenKeywordHiding
    | TokenKeywordRecord
    | TokenKeywordClass
    | TokenKeywordInstance
    | TokenKeywordInt
    | TokenKeywordFloat
    | TokenKeywordChar
    | TokenKeywordString
    | TokenNatural Integer
    | TokenFloat Double
    | TokenChar Char
    | TokenString Text
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
    | UnterminatedString !SourcePos
    | InvalidEscape !SourcePos !Char
    | InvalidCharLiteral !SourcePos
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
    TokenDot           -> "'.'"
    TokenKeywordModule -> "'module'"
    TokenKeywordImport -> "'import'"
    TokenKeywordQualified -> "'qualified'"
    TokenKeywordHiding -> "'hiding'"
    TokenKeywordRecord -> "'record'"
    TokenKeywordClass -> "'class'"
    TokenKeywordInstance -> "'instance'"
    TokenKeywordInt -> "'Int'"
    TokenKeywordFloat -> "'Float'"
    TokenKeywordChar -> "'Char'"
    TokenKeywordString -> "'String'"
    TokenNatural n -> Text.pack (show n)
    TokenFloat n -> Text.pack (show n)
    TokenChar c -> "'" <> Text.singleton c <> "'"
    TokenString s -> "\"" <> s <> "\""
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

-- | A `.` lexes as `TokenDot` (for `r.field` / `Module.name`) only when it is
-- not surrounded by whitespace: prev non-space char must be identifier-like
-- (letter/digit/`_`/`)``]`/`}`) and next char must be identifier-like.
isDotOp :: Char -> Char -> Bool
isDotOp prevNxt nextChar =
    isDotPrev prevNxt && isIdentStart nextChar
  where
    isDotPrev c = isAlphaNum c || c == '_' || c `elem` [')', ']', '}']
    isIdentStart c = isAlphaNum c || c == '_'

tokenize :: Text -> Either LexError [PosToken]
tokenize sourceText = scanLoop initialPos (Text.unpack sourceText) ' '
  where
    scanLoop _ [] _ = Right []
    scanLoop pos remaining@(headChar : rest) prevNonSpace
        | isSpace headChar =
            scanLoop (advancePosChar pos headChar) rest ' '
        | take 2 remaining == "--" =
            let (comment, restAfter) = span (/= '\n') remaining
                pos' = advancePosString pos comment
             in scanLoop pos' restAfter prevNonSpace
        | take 2 remaining == "{-" =
            case skipBlockComment (advancePosString pos "{-") (1 :: Int) (drop 2 remaining) of
                Left err -> Left err
                Right (pos', afterBlock) -> scanLoop pos' afterBlock prevNonSpace
        | Just (arrowStr, restAfter) <- matchPrefixDFA dfaArrow remaining =
            let pos' = advancePosString pos arrowStr
             in (PosToken pos TokenArrow :) <$> scanLoop pos' restAfter '-'
        | headChar == '"' = do
            (value, pos', restAfter) <- scanQuoted pos '"' rest
            (PosToken pos (TokenString (Text.pack value)) :) <$> scanLoop pos' restAfter '"'
        | headChar == '\'' = do
            (value, pos', restAfter) <- scanQuoted pos '\'' rest
            case value of
                [c] -> (PosToken pos (TokenChar c) :) <$> scanLoop pos' restAfter '\''
                _ -> Left (InvalidCharLiteral pos)
        | Just (floatValue, rawFloat, restAfter) <- scanFloat remaining =
            let pos' = advancePosString pos rawFloat
             in (PosToken pos (TokenFloat floatValue) :) <$> scanLoop pos' restAfter (last rawFloat)
        | Just (numStr, restAfter) <- matchPrefixDFA dfaNatural remaining =
            let n = read numStr :: Integer
                pos' = advancePosString pos numStr
             in (PosToken pos (TokenNatural n) :) <$> scanLoop pos' restAfter '-'
        | headChar == '?' =
            let (identChars, restAfter) = span (\c -> isAlphaNum c || c == '_') rest
                mIdent = if null identChars then Nothing else Just (Identifier (Text.pack identChars))
                consumed = headChar : identChars
                pos' = advancePosString pos consumed
             in (PosToken pos (TokenHole mIdent) :) <$> scanLoop pos' restAfter '?'
        | headChar == '.' && not (null rest) && isDotOp prevNonSpace (head rest) =
            let pos' = advancePosChar pos headChar
             in (PosToken pos TokenDot :) <$> scanLoop pos' rest '.'
        | Just (identStr, restAfter) <- matchPrefixDFA dfaIdentifier remaining =
            let token = classifyIdentifier (Text.pack identStr)
                pos' = advancePosString pos identStr
             in (PosToken pos token :) <$> scanLoop pos' restAfter (last identStr)
        | headChar `elem` opSymbols =
            let (opStr, restAfter) = span (`elem` opSymbols) remaining
                pos' = advancePosString pos opStr
                token = case opStr of
                    "=" -> TokenEquals
                    "|" -> TokenPipe
                    _ -> TokenOperator (Identifier (Text.pack opStr))
             in (PosToken pos token :) <$> scanLoop pos' restAfter (last opStr)
        | otherwise =
            case headChar of
                '\\' -> (PosToken pos TokenBackslash :) <$> scanLoop (advancePosChar pos headChar) rest '\\'
                ':' -> (PosToken pos TokenColon :) <$> scanLoop (advancePosChar pos headChar) rest ':'
                ';' -> (PosToken pos TokenSemicolon :) <$> scanLoop (advancePosChar pos headChar) rest ';'
                '(' -> (PosToken pos TokenLeftParen :) <$> scanLoop (advancePosChar pos headChar) rest '('
                ')' -> (PosToken pos TokenRightParen :) <$> scanLoop (advancePosChar pos headChar) rest ')'
                '[' -> (PosToken pos TokenLeftBracket :) <$> scanLoop (advancePosChar pos headChar) rest '['
                ']' -> (PosToken pos TokenRightBracket :) <$> scanLoop (advancePosChar pos headChar) rest ']'
                '{' -> (PosToken pos TokenLeftBrace :) <$> scanLoop (advancePosChar pos headChar) rest '{'
                '}' -> (PosToken pos TokenRightBrace :) <$> scanLoop (advancePosChar pos headChar) rest '}'
                ',' -> (PosToken pos TokenComma :) <$> scanLoop (advancePosChar pos headChar) rest ','
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
        "record" -> TokenKeywordRecord
        "class" -> TokenKeywordClass
        "instance" -> TokenKeywordInstance
        "Int" -> TokenKeywordInt
        "Float" -> TokenKeywordFloat
        "Char" -> TokenKeywordChar
        "String" -> TokenKeywordString
        "module" -> TokenKeywordModule
        "import" -> TokenKeywordImport
        "qualified" -> TokenKeywordQualified
        "hiding" -> TokenKeywordHiding
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

    scanFloat input =
        let (whole, afterWhole) = span isDigit input
            withFraction = case afterWhole of
                '.' : afterDot ->
                    let (fraction, afterFraction) = span isDigit afterDot
                     in if null whole || null fraction then Nothing else Just (whole <> "." <> fraction, afterFraction)
                _ -> Nothing
            withExponent = case afterWhole of
                e : afterE | e == 'e' || e == 'E' ->
                    let (sign, afterSign) = case afterE of
                            s : xs | s == '+' || s == '-' -> ([s], xs)
                            _ -> ([], afterE)
                        (digits, rest) = span isDigit afterSign
                     in if null whole || null digits then Nothing else Just (whole <> [e] <> sign <> digits, rest)
                _ -> Nothing
            candidate = case withFraction of
                Just (raw, rest) -> Just (raw, rest)
                Nothing -> withExponent
         in case candidate of
                Just (raw, rest) -> Just (read raw, raw, rest)
                Nothing -> Nothing

    scanQuoted start quote input = go (advancePosChar start quote) input []
      where
        go pos [] _ = Left (UnterminatedString start)
        go pos (c : cs) acc
            | c == quote = Right (reverse acc, advancePosChar pos c, cs)
            | c == '\\' = do
                (decoded, pos', rest) <- scanEscape pos cs
                go pos' rest (decoded : acc)
            | c == '\n' = Left (UnterminatedString pos)
            | otherwise = go (advancePosChar pos c) cs (c : acc)

    scanEscape pos [] = Left (UnterminatedString pos)
    scanEscape pos (c : cs) = case c of
        'n' -> Right ('\n', advancePosString pos "\\n", cs)
        't' -> Right ('\t', advancePosString pos "\\t", cs)
        'r' -> Right ('\r', advancePosString pos "\\r", cs)
        '\\' -> Right ('\\', advancePosString pos "\\\\", cs)
        '"' -> Right ('"', advancePosString pos "\\\"", cs)
        '\'' -> Right ('\'', advancePosString pos "\\'", cs)
        '0' -> Right ('\0', advancePosString pos "\\0", cs)
        'x' -> numericEscape pos 2 16 cs
        'u' -> numericEscape pos 4 16 cs
        other -> Left (InvalidEscape pos other)

    numericEscape pos count base chars =
        let (digits, rest) = splitAt count chars
         in if length digits == count && all isHexDigit digits
                then Right (chr (foldl (\n c -> n * base + digitToInt c) 0 digits), advancePosString pos ('\\' : take 1 chars <> digits), rest)
                else Left (InvalidEscape pos (if null chars then '\\' else head chars))

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
    UnterminatedString pos ->
        "Lexical error at line " <> Text.pack (show (posLine pos)) <> ", col " <> Text.pack (show (posColumn pos)) <> ": Unterminated string or character literal"
    InvalidEscape pos c ->
        "Lexical error at line " <> Text.pack (show (posLine pos)) <> ", col " <> Text.pack (show (posColumn pos)) <> ": Invalid escape '\\" <> Text.singleton c <> "'"
    InvalidCharLiteral pos ->
        "Lexical error at line " <> Text.pack (show (posLine pos)) <> ", col " <> Text.pack (show (posColumn pos)) <> ": Invalid character literal"
