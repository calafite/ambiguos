{-# LANGUAGE OverloadedStrings #-}

module Parser (
    ParseError (..),
    parseExpression,
    parseStatement,
    parseProgram,
    renderParseError,
    renderParseErrorWithSource,
) where

import AST (CaseBranch (..), Expression (..), Identifier (..), Statement (..), Visibility (..))
import Control.Applicative (Alternative (..), optional)
import Data.Text (Text)
import qualified Data.Text as Text
import Lexer (
    LexError (..),
    PosToken (..),
    SourcePos (..),
    Token (..),
    prettyToken,
    renderLexError,
    tokenize,
  )
import Diagnostics (SourceSpan (..), formatSourceSnippet)

data ParseError
    = ErrorLexical !LexError
    | UnexpectedEndOfInput !(Maybe SourcePos)
    | ExpectedToken !Text !Token !SourcePos
    | UnexpectedToken !Token !SourcePos
    deriving (Eq, Show)

newtype Parser a = Parser
    { runParser :: [PosToken] -> Either ParseError (a, [PosToken])
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
    empty = Parser $ \tokens ->
        let mPos = case tokens of
                (PosToken pos _ : _) -> Just pos
                [] -> Nothing
         in Left (UnexpectedEndOfInput mPos)
    Parser p1 <|> Parser p2 = Parser $ \tokens ->
        case p1 tokens of
            Right result -> Right result
            Left _ -> p2 tokens

instance Monad Parser where
    Parser p >>= f = Parser $ \tokens -> do
        (val, remaining) <- p tokens
        runParser (f val) remaining

-- | Wraps the parsed expression in a `Located` node spanning from the first
-- consumed token's position up to the position of the first unconsumed token.
withSpan :: Parser Expression -> Parser Expression
withSpan (Parser p) = Parser $ \tokens -> case tokens of
    [] -> p tokens
    (PosToken start _ : _) ->
        case p tokens of
            Right (expr, remaining) ->
                let end = case remaining of
                        [] -> start
                        (PosToken pos _ : _) -> pos
                 in Right (Located (SourceSpan start end) expr, remaining)
            result -> result

peekToken :: Parser (Maybe Token)
peekToken = Parser $ \tokens -> case tokens of
    [] -> Right (Nothing, [])
    (PosToken _ t : _) -> Right (Just t, tokens)

peekPosToken :: Parser (Maybe PosToken)
peekPosToken = Parser $ \tokens -> case tokens of
    [] -> Right (Nothing, [])
    (pt : _) -> Right (Just pt, tokens)

consumeToken :: Parser PosToken
consumeToken = Parser $ \tokens -> case tokens of
    [] -> Left (UnexpectedEndOfInput Nothing)
    (pt : ts) -> Right (pt, ts)

expectToken :: Token -> Text -> Parser ()
expectToken expected description = do
    mNext <- peekPosToken
    case mNext of
        Just (PosToken pos t)
            | t == expected -> do
                _ <- consumeToken
                pure ()
            | otherwise -> Parser $ \_ -> Left (ExpectedToken description t pos)
        Nothing -> Parser $ \_ -> Left (UnexpectedEndOfInput Nothing)

parseIdentifier :: Parser Identifier
parseIdentifier = parseNamed <|> parseParenOp
  where
    parseNamed = do
        mPt <- peekPosToken
        case mPt of
            Just (PosToken _ (TokenIdentifier ident)) -> do
                _ <- consumeToken
                pure ident
            Just (PosToken _ (TokenOperator ident)) -> do
                _ <- consumeToken
                pure ident
            Just (PosToken _ (TokenHole Nothing)) -> do
                _ <- consumeToken
                pure (Identifier "_")
            Just (PosToken _ (TokenHole (Just (Identifier name)))) -> do
                _ <- consumeToken
                pure (Identifier ("_" <> name))
            Just (PosToken _ TokenKeywordZero) -> do
                _ <- consumeToken
                pure (Identifier "zero")
            Just (PosToken _ TokenKeywordSucc) -> do
                _ <- consumeToken
                pure (Identifier "successor")
            _ -> empty

    parseParenOp = do
        mPt <- peekPosToken
        case mPt of
            Just (PosToken _ TokenLeftParen) -> do
                _ <- consumeToken
                pt <- consumeToken
                case tokenValue pt of
                    TokenOperator ident -> do
                        expectToken TokenRightParen "')'"
                        pure ident
                    other -> Parser $ \_ -> Left (ExpectedToken "operator" other (tokenPos pt))
            _ -> empty

desugarNatural :: Integer -> Expression
desugarNatural n
    | n <= 0 = Zero
    | otherwise = Application Explicit Succ (desugarNatural (n - 1))

desugarList :: [Expression] -> Expression
desugarList [] = Variable (Identifier "nil")
desugarList (x : xs) =
    Application
        Explicit
        (Application Explicit (Variable (Identifier "cons")) x)
        (desugarList xs)

parseListElements :: Parser [Expression]
parseListElements = do
    firstElem <- expressionParser
    restElems <- many (expectToken TokenComma "','" *> expressionParser)
    pure (firstElem : restElems)

parseListLiteral :: Parser Expression
parseListLiteral = do
    _ <- consumeToken
    nextToken <- peekToken
    case nextToken of
        Just TokenRightBracket -> do
            _ <- consumeToken
            pure (desugarList [])
        _ -> do
            elems <- parseListElements
            expectToken TokenRightBracket "']'"
            pure (desugarList elems)

parseAtomicExpression :: Parser Expression
parseAtomicExpression = do
    mPt <- peekPosToken
    case mPt of
        Just (PosToken _ TokenKeywordType) -> do
            _ <- consumeToken
            nextTok <- peekToken
            case nextTok of
                Just (TokenNatural n) -> do
                    _ <- consumeToken
                    pure (Universe (fromInteger n))
                _ -> pure (Universe (-1))
        Just (PosToken _ TokenKeywordId) -> Identity <$ consumeToken
        Just (PosToken _ TokenKeywordRefl) -> Reflexivity <$ consumeToken
        Just (PosToken _ TokenKeywordJ) -> J <$ consumeToken
        Just (PosToken _ TokenKeywordVoid) -> VoidType <$ consumeToken
        Just (PosToken _ TokenKeywordAbort) -> Abort <$ consumeToken
        Just (PosToken _ TokenKeywordNat) -> NatType <$ consumeToken
        Just (PosToken _ TokenKeywordZero) -> Zero <$ consumeToken
        Just (PosToken _ TokenKeywordSucc) -> Succ <$ consumeToken
        Just (PosToken _ TokenKeywordNatRec) -> NatRec <$ consumeToken
        Just (PosToken _ (TokenNatural n)) -> desugarNatural n <$ consumeToken
        Just (PosToken _ (TokenHole mIdent)) -> Hole mIdent <$ consumeToken
        Just (PosToken _ (TokenIdentifier ident)) -> Variable ident <$ consumeToken
        Just (PosToken _ TokenLeftBracket) -> parseListLiteral
        Just (PosToken _ TokenLeftParen) -> do
            _ <- consumeToken
            nextTok <- peekToken
            case nextTok of
                Just (TokenOperator op) -> do
                    _ <- consumeToken
                    expectToken TokenRightParen "')'"
                    pure (Variable op)
                _ -> do
                    expr <- expressionParser
                    expectToken TokenRightParen "')'"
                    pure expr
        Just (PosToken pos other) -> Parser $ \_ -> Left (UnexpectedToken other pos)
        Nothing -> Parser $ \_ -> Left (UnexpectedEndOfInput Nothing)

parseAppArgument :: Parser (Visibility, Expression)
parseAppArgument = parseImplicitOverride <|> parseExplicitArg
  where
    parseImplicitOverride = do
        expectToken TokenLeftBrace "'{'"
        expr <- expressionParser
        expectToken TokenRightBrace "'}'"
        pure (Implicit, expr)
    parseExplicitArg = do
        expr <- parseAtomicExpression
        pure (Explicit, expr)

parseApplication :: Parser Expression
parseApplication = do
    headExpr <- parseAtomicExpression
    argExprs <- many parseAppArgument
    pure (foldl (\acc (vis, arg) -> Application vis acc arg) headExpr argExprs)

parseDependentArrow :: Parser Expression
parseDependentArrow = parseExplicit <|> parseImplicit
  where
    parseExplicit = do
        expectToken TokenLeftParen "'('"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser
        expectToken TokenRightParen "')'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser
        pure (foldr (\name acc -> Pi Explicit name domainType acc) codomainType parameterNames)

    parseImplicit = do
        expectToken TokenLeftBrace "'{'"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser
        expectToken TokenRightBrace "'}'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser
        pure (foldr (\name acc -> Pi Implicit name domainType acc) codomainType parameterNames)

parseNonDependentArrow :: Parser Expression
parseNonDependentArrow = do
    domain <- parseApplication
    isArrow <- (True <$ expectToken TokenArrow "'->'") <|> pure False
    if isArrow
        then do
            codomain <- expressionParser
            pure (Pi Explicit (Identifier "_") domain codomain)
        else pure domain

parseArrowOrApplication :: Parser Expression
parseArrowOrApplication = parseDependentArrow <|> parseNonDependentArrow

parseInfix :: Parser Expression
parseInfix = do
    left <- parseArrowOrApplication
    rest <- many parseOpRight
    pure (foldl (\acc (op, right) -> Application Explicit (Application Explicit (Variable op) acc) right) left rest)
  where
    parseOpRight = do
        nextTok <- peekToken
        case nextTok of
            Just (TokenOperator op) -> do
                _ <- consumeToken
                right <- parseArrowOrApplication
                pure (op, right)
            _ -> empty

parseAnnotation :: Parser Expression
parseAnnotation = do
    termExpr <- parseInfix
    isAnnotated <- (True <$ expectToken TokenColon "':'") <|> pure False
    if isAnnotated
        then do
            annType <- expressionParser
            pure (Annotation termExpr annType)
        else pure termExpr

data ParameterGroup
    = SimpleParameters [Identifier]
    | TypedParameters Visibility [Identifier] Expression

parseParameterGroup :: Parser ParameterGroup
parseParameterGroup = parseTypedParen <|> parseTypedBrace <|> parseSimple
  where
    parseTypedParen = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser
        expectToken TokenRightParen "')'"
        pure (TypedParameters Explicit names paramType)

    parseTypedBrace = do
        expectToken TokenLeftBrace "'{'"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser
        expectToken TokenRightBrace "'}'"
        pure (TypedParameters Implicit names paramType)

    parseSimple = do
        names <- some parseIdentifier
        pure (SimpleParameters names)

parseLambda :: Parser Expression
parseLambda = do
    expectToken TokenBackslash "'\\'"
    paramGroups <- some parseParameterGroup
    expectToken TokenArrow "'->'"
    body <- expressionParser
    pure (foldr expandGroup body paramGroups)
  where
    expandGroup (SimpleParameters names) acc =
        foldr (\name inner -> Lambda Explicit name Nothing inner) acc names
    expandGroup (TypedParameters vis names pType) acc =
        foldr (\name inner -> Lambda vis name (Just pType) inner) acc names

parseLet :: Parser Expression
parseLet = do
    expectToken TokenKeywordLet "'let'"
    name <- parseIdentifier
    maybeType <- optional (expectToken TokenColon "':'" *> expressionParser)
    expectToken TokenEquals "'='"
    valExpr <- expressionParser
    expectToken TokenKeywordIn "'in'"
    bodyExpr <- expressionParser
    pure (Let name maybeType valExpr bodyExpr)

parseCaseBranch :: Parser CaseBranch
parseCaseBranch = do
    con <- parseIdentifier
    bindings <- many parseIdentifier
    expectToken TokenArrow "'->'"
    body <- expressionParser
    pure (CaseBranch con bindings body)

parseCase :: Parser Expression
parseCase = do
    expectToken TokenKeywordCase "'case'"
    target <- expressionParser
    expectToken TokenKeywordOf "'of'"
    nextTok <- peekToken
    branches <- case nextTok of
        Just TokenLeftBrace -> parseBraced
        _ -> parsePiped
    pure (Case target branches)
  where
    parseBraced = do
        expectToken TokenLeftBrace "'{'"
        bs <- many (parseCaseBranch <* optional (expectToken TokenSemicolon "';'"))
        expectToken TokenRightBrace "'}'"
        pure bs
    parsePiped = do
        _ <- optional (expectToken TokenPipe "'|'")
        b1 <- parseCaseBranch
        bs <- many (expectToken TokenPipe "'|'" *> parseCaseBranch)
        pure (b1 : bs)

expressionParser :: Parser Expression
expressionParser = withSpan $ do
    nextTok <- peekToken
    case nextTok of
        Just TokenBackslash -> parseLambda
        Just TokenKeywordLet -> parseLet
        Just TokenKeywordCase -> parseCase
        _ -> parseAnnotation

parseDataParameter :: Parser [(Visibility, Identifier, Expression)]
parseDataParameter = parseExplicit <|> parseImplicit
  where
    parseExplicit = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        ty <- expressionParser
        expectToken TokenRightParen "')'"
        pure [(Explicit, n, ty) | n <- names]
    parseImplicit = do
        expectToken TokenLeftBrace "'{'"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        ty <- expressionParser
        expectToken TokenRightBrace "'}'"
        pure [(Implicit, n, ty) | n <- names]

parseConstructorDecl :: Parser (Identifier, Expression)
parseConstructorDecl = do
    cName <- parseIdentifier
    expectToken TokenColon "':'"
    cType <- expressionParser
    pure (cName, cType)

parseDataDeclaration :: Parser Statement
parseDataDeclaration = do
    expectToken TokenKeywordData "'data'"
    name <- parseIdentifier
    paramGroups <- many parseDataParameter
    expectToken TokenColon "':'"
    univ <- expressionParser
    expectToken TokenKeywordWhere "'where'"
    constrs <- parseBraced <|> many parseConstructorDecl
    pure (DataDeclaration name (concat paramGroups) univ constrs)
  where
    parseBraced = do
        expectToken TokenLeftBrace "'{'"
        cs <- many (parseConstructorDecl <* optional (expectToken TokenSemicolon "';'"))
        expectToken TokenRightBrace "'}'"
        pure cs

parseDefinition :: Parser Statement
parseDefinition = do
    expectToken TokenKeywordDef "'def'"
    name <- parseIdentifier
    maybeType <- optional (expectToken TokenColon "':'" *> expressionParser)
    expectToken TokenEquals "'='"
    bodyTerm <- expressionParser
    pure (Definition name maybeType bodyTerm)

parseEvaluation :: Parser Statement
parseEvaluation = Evaluation <$> expressionParser

statementParser :: Parser Statement
statementParser = do
    nextTok <- peekToken
    case nextTok of
        Just TokenKeywordData -> parseDataDeclaration
        Just TokenKeywordDef -> parseDefinition
        _ -> parseEvaluation

runCompleteParser :: Parser a -> [PosToken] -> Either ParseError a
runCompleteParser parser tokens =
    case runParser parser tokens of
        Right (result, []) -> Right result
        Right (_, PosToken pos unconsumed : _) -> Left (UnexpectedToken unconsumed pos)
        Left err -> Left err

parseExpression :: Text -> Either ParseError Expression
parseExpression input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    runCompleteParser expressionParser tokens

parseStatement :: Text -> Either ParseError Statement
parseStatement input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    runCompleteParser statementParser tokens

parseProgram :: Text -> Either ParseError [Statement]
parseProgram input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    parseAll tokens
  where
    parseAll [] = Right []
    parseAll toks@(PosToken pos t : _) = do
        (stmt, rest) <- runParser statementParser toks
        if length rest == length toks
            then Left (UnexpectedToken t pos)
            else (stmt :) <$> parseAll rest

renderParseError :: ParseError -> Text
renderParseError = renderParseErrorWithSource Nothing Nothing

renderParseErrorWithSource :: Maybe FilePath -> Maybe Text -> ParseError -> Text
renderParseErrorWithSource mFile mSource err = case err of
    ErrorLexical lexErr -> case mSource of
        Just src ->
            let pos = case lexErr of
                    UnexpectedCharacter p _ -> p
                    UnterminatedBlockComment p -> p
                msg = renderLexError lexErr
             in formatSourceSnippet mFile src (SourceSpan pos pos) msg
        Nothing -> renderLexError lexErr
    UnexpectedEndOfInput mPos ->
        let loc = formatLoc mFile mPos
         in loc <> "Syntax error: Unexpected end of input."
    ExpectedToken expected found pos ->
        let msg = "Syntax error: Expected " <> expected <> ", but found " <> prettyToken found
         in case mSource of
                Just src -> formatSourceSnippet mFile src (SourceSpan pos pos) msg
                Nothing -> formatLoc mFile (Just pos) <> msg
    UnexpectedToken token pos ->
        let msg = "Syntax error: Unexpected token " <> prettyToken token
         in case mSource of
                Just src -> formatSourceSnippet mFile src (SourceSpan pos pos) msg
                Nothing -> formatLoc mFile (Just pos) <> msg
  where
    formatLoc (Just fp) (Just pos) =
        Text.pack fp <> ":" <> Text.pack (show (posLine pos)) <> ":" <> Text.pack (show (posColumn pos)) <> ": "
    formatLoc Nothing (Just pos) =
        "Line " <> Text.pack (show (posLine pos)) <> ", col " <> Text.pack (show (posColumn pos)) <> ": "
    formatLoc (Just fp) Nothing = Text.pack fp <> ": "
    formatLoc Nothing Nothing = ""
