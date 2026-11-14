{-# LANGUAGE OverloadedStrings #-}

module Parser (
    ParseError (..),
    FixityEnv,
    defaultFixityEnv,
    fixityOf,    parseExpression,
    parseExpressionWith,
    parseStatement,
    parseStatementWith,
    parseProgram,
    parseProgramWith,
    renderParseError,
    renderParseErrorWithSource,
) where

import AST (CaseBranch (..), Expression (..), Identifier (..), Statement (..), Visibility (..), Associativity (..), Fixity (..))
import Control.Applicative (Alternative (..), optional)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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

-- | Environment mapping operators to their declared fixity.
type FixityEnv = Map Identifier Fixity

-- | Default fixity environment matching standard math and prelude.amb operators.
defaultFixityEnv :: FixityEnv
defaultFixityEnv = Map.fromList
    [ (Identifier ".", Fixity AssocRight 9)
    , (Identifier "^", Fixity AssocRight 8)
    , (Identifier "*", Fixity AssocLeft 7)
    , (Identifier "+", Fixity AssocLeft 6)
    , (Identifier "-", Fixity AssocLeft 6)
    , (Identifier "++", Fixity AssocRight 5)
    , (Identifier "==", Fixity AssocNone 4)
    , (Identifier "/=", Fixity AssocNone 4)
    , (Identifier "<", Fixity AssocNone 4)
    , (Identifier "<=", Fixity AssocNone 4)
    , (Identifier ">", Fixity AssocNone 4)
    , (Identifier ">=", Fixity AssocNone 4)
    , (Identifier "&&", Fixity AssocRight 3)
    , (Identifier "||", Fixity AssocRight 2)
    , (Identifier "$", Fixity AssocRight 0)
    ]

fixityOf :: FixityEnv -> Identifier -> Fixity
fixityOf env op = Map.findWithDefault (Fixity AssocLeft 9) op env

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

desugarNatural :: Integer -> Expression

-- | Parse a parenthesized operator, e.g. `(+)`.
parseParenOp :: Parser Identifier
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

parseListElements :: FixityEnv -> Parser [Expression]
parseListElements env = do
    firstElem <- expressionParser env
    restElems <- many (expectToken TokenComma "','" *> expressionParser env)
    pure (firstElem : restElems)

parseListLiteral :: FixityEnv -> Parser Expression
parseListLiteral env = do
    _ <- consumeToken
    nextToken <- peekToken
    case nextToken of
        Just TokenRightBracket -> do
            _ <- consumeToken
            pure (desugarList [])
        _ -> do
            elems <- parseListElements env
            expectToken TokenRightBracket "']'"
            pure (desugarList elems)

parseAtomicExpression :: FixityEnv -> Parser Expression
parseAtomicExpression env = do
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
        Just (PosToken _ TokenLeftBracket) -> parseListLiteral env
        Just (PosToken _ TokenLeftParen) -> do
            _ <- consumeToken
            nextTok <- peekToken
            case nextTok of
                Just (TokenOperator op) -> do
                    _ <- consumeToken
                    expectToken TokenRightParen "')'"
                    pure (Variable op)
                _ -> do
                    expr <- expressionParser env
                    expectToken TokenRightParen "')'"
                    pure expr
        Just (PosToken pos other) -> Parser $ \_ -> Left (UnexpectedToken other pos)
        Nothing -> Parser $ \_ -> Left (UnexpectedEndOfInput Nothing)

parseAppArgument :: FixityEnv -> Parser (Visibility, Expression)
parseAppArgument env = parseImplicitOverride <|> parseExplicitArg env
  where
    parseImplicitOverride = do
        expectToken TokenLeftBrace "'{'"
        expr <- expressionParser env
        expectToken TokenRightBrace "'}'"
        pure (Implicit, expr)
    parseExplicitArg e = do
        expr <- parseAtomicExpression e
        pure (Explicit, expr)

parseApplication :: FixityEnv -> Parser Expression
parseApplication env = do
    headExpr <- parseAtomicExpression env
    argExprs <- many (parseAppArgument env)
    pure (foldl (\acc (vis, arg) -> Application vis acc arg) headExpr argExprs)

parseDependentArrow :: FixityEnv -> Parser Expression
parseDependentArrow env = parseExplicit <|> parseImplicit
  where
    parseExplicit = do
        expectToken TokenLeftParen "'('"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser env
        expectToken TokenRightParen "')'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser env
        pure (foldr (\name acc -> Pi Explicit name domainType acc) codomainType parameterNames)

    parseImplicit = do
        expectToken TokenLeftBrace "'{'"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser env
        expectToken TokenRightBrace "'}'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser env
        pure (foldr (\name acc -> Pi Implicit name domainType acc) codomainType parameterNames)

parseNonDependentArrow :: FixityEnv -> Parser Expression
parseNonDependentArrow env = do
    domain <- parseInfix env 0
    isArrow <- (True <$ expectToken TokenArrow "'->'") <|> pure False
    if isArrow
        then do
            codomain <- expressionParser env
            pure (Pi Explicit (Identifier "_") domain codomain)
        else pure domain

parseArrowOrApplication :: FixityEnv -> Parser Expression
parseArrowOrApplication env = parseDependentArrow env <|> parseNonDependentArrow env

-- | Precedence-climbing parser for infix operators.
-- `minPrec` is the minimum precedence an operator must have to be consumed.
parseInfix :: FixityEnv -> Int -> Parser Expression
parseInfix env minPrec = do
    left <- parseApplication env
    precLoop left minPrec
  where
    precLoop left curMin = do
        mOp <- peekOperatorFixity env
        case mOp of
            Just (op, p, assoc) | p >= curMin -> do
                _ <- consumeToken
                let nextMin = case assoc of
                        AssocLeft -> p + 1
                        AssocRight -> p
                        AssocNone -> p + 1
                right <- parseInfix env nextMin
                -- For non-associative operators, reject chaining at the same level.
                let contMin = case assoc of
                        AssocNone -> p + 1
                        _ -> curMin
                precLoop (Application Explicit (Application Explicit (Variable op) left) right) contMin
            _ -> pure left

    peekOperatorFixity :: FixityEnv -> Parser (Maybe (Identifier, Int, Associativity))
    peekOperatorFixity e = do
        mPt <- peekPosToken
        case mPt of
            Just (PosToken _ (TokenOperator op)) ->
                let f = fixityOf e op
                 in pure (Just (op, fixityPrec f, fixityAssoc f))
            _ -> pure Nothing

parseAnnotation :: FixityEnv -> Parser Expression
parseAnnotation env = do
    termExpr <- parseArrowOrApplication env
    isAnnotated <- (True <$ expectToken TokenColon "':'") <|> pure False
    if isAnnotated
        then do
            annType <- expressionParser env
            pure (Annotation termExpr annType)
        else pure termExpr

data ParameterGroup
    = SimpleParameters [Identifier]
    | TypedParameters Visibility [Identifier] Expression

parseParameterGroup :: FixityEnv -> Parser ParameterGroup
parseParameterGroup env = parseTypedParen <|> parseTypedBrace <|> parseSimple
  where
    parseTypedParen = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser env
        expectToken TokenRightParen "')'"
        pure (TypedParameters Explicit names paramType)

    parseTypedBrace = do
        expectToken TokenLeftBrace "'{'"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser env
        expectToken TokenRightBrace "'}'"
        pure (TypedParameters Implicit names paramType)

    parseSimple = do
        names <- some parseIdentifier
        pure (SimpleParameters names)

parseLambda :: FixityEnv -> Parser Expression
parseLambda env = do
    expectToken TokenBackslash "'\\'"
    paramGroups <- some (parseParameterGroup env)
    expectToken TokenArrow "'->'"
    body <- expressionParser env
    pure (foldr expandGroup body paramGroups)
  where
    expandGroup (SimpleParameters names) acc =
        foldr (\name inner -> Lambda Explicit name Nothing inner) acc names
    expandGroup (TypedParameters vis names pType) acc =
        foldr (\name inner -> Lambda vis name (Just pType) inner) acc names

parseLet :: FixityEnv -> Parser Expression
parseLet env = do
    expectToken TokenKeywordLet "'let'"
    name <- parseIdentifier
    maybeType <- optional (expectToken TokenColon "':'" *> expressionParser env)
    expectToken TokenEquals "'='"
    valExpr <- expressionParser env
    expectToken TokenKeywordIn "'in'"
    bodyExpr <- expressionParser env
    pure (Let name maybeType valExpr bodyExpr)

parseCaseBranch :: FixityEnv -> Parser CaseBranch
parseCaseBranch env = do
    con <- parseIdentifier
    bindings <- many parseIdentifier
    expectToken TokenArrow "'->'"
    body <- expressionParser env
    pure (CaseBranch con bindings body)

parseCase :: FixityEnv -> Parser Expression
parseCase env = do
    expectToken TokenKeywordCase "'case'"
    target <- expressionParser env
    mMotive <- parseMotive
    expectToken TokenKeywordOf "'of'"
    nextTok <- peekToken
    branches <- case nextTok of
        Just TokenLeftBrace -> parseBraced
        _ -> parsePiped
    pure (Case target mMotive branches)
  where
    parseMotive :: Parser (Maybe (Identifier, Expression))
    parseMotive = do
        nextTok <- peekToken
        case nextTok of
            Just TokenKeywordAs -> do
                _ <- consumeToken
                mv <- parseIdentifier
                expectToken TokenKeywordReturn "'return'"
                mt <- expressionParser env
                pure (Just (mv, mt))
            _ -> pure Nothing
    parseBraced = do
        expectToken TokenLeftBrace "'{'"
        bs <- many (parseCaseBranch env <* optional (expectToken TokenSemicolon "';'"))
        expectToken TokenRightBrace "'}'"
        pure bs
    parsePiped = do
        _ <- optional (expectToken TokenPipe "'|'")
        b1 <- parseCaseBranch env
        bs <- many (expectToken TokenPipe "'|'" *> parseCaseBranch env)
        pure (b1 : bs)

expressionParser :: FixityEnv -> Parser Expression
expressionParser env = withSpan $ do
    nextTok <- peekToken
    case nextTok of
        Just TokenBackslash -> parseLambda env
        Just TokenKeywordLet -> parseLet env
        Just TokenKeywordCase -> parseCase env
        _ -> parseAnnotation env

parseDataParameter :: FixityEnv -> Parser [(Visibility, Identifier, Expression)]
parseDataParameter env = parseExplicit <|> parseImplicit
  where
    parseExplicit = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        ty <- expressionParser env
        expectToken TokenRightParen "')'"
        pure [(Explicit, n, ty) | n <- names]
    parseImplicit = do
        expectToken TokenLeftBrace "'{'"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        ty <- expressionParser env
        expectToken TokenRightBrace "'}'"
        pure [(Implicit, n, ty) | n <- names]

parseConstructorDecl :: FixityEnv -> Parser (Identifier, Expression)
parseConstructorDecl env = do
    cName <- parseIdentifier
    expectToken TokenColon "':'"
    cType <- expressionParser env
    pure (cName, cType)

parseFixityOp :: Parser Identifier
parseFixityOp = parseParenOp <|> parseOperatorIdent
  where
    parseOperatorIdent = do
        mPt <- peekPosToken
        case mPt of
            Just (PosToken _ (TokenOperator op)) -> do
                _ <- consumeToken
                pure op
            _ -> empty

parseFixityDeclaration :: FixityEnv -> Parser Statement
parseFixityDeclaration _env = do
    assoc <- (AssocLeft <$ expectToken TokenKeywordInfixL "'infixl'")
        <|> (AssocRight <$ expectToken TokenKeywordInfixR "'infixr'")
        <|> (AssocNone <$ expectToken TokenKeywordInfix "'infix'")
    mPt <- peekPosToken
    case mPt of
        Just (PosToken _ (TokenNatural n)) -> do
            _ <- consumeToken
            let prec = fromInteger n
            ops <- many parseFixityOp
            pure (FixityDeclaration assoc prec ops)
        _ -> Parser $ \_ -> Left (UnexpectedEndOfInput Nothing)

parseDataDeclaration :: FixityEnv -> Parser Statement
parseDataDeclaration env = do
    expectToken TokenKeywordData "'data'"
    name <- parseIdentifier
    paramGroups <- many (parseDataParameter env)
    expectToken TokenColon "':'"
    univ <- expressionParser env
    expectToken TokenKeywordWhere "'where'"
    constrs <- parseBraced <|> many (parseConstructorDecl env)
    pure (DataDeclaration name (concat paramGroups) univ constrs)
  where
    parseBraced = do
        expectToken TokenLeftBrace "'{'"
        cs <- many (parseConstructorDecl env <* optional (expectToken TokenSemicolon "';'"))
        expectToken TokenRightBrace "'}'"
        pure cs

parseDefinition :: FixityEnv -> Parser Statement
parseDefinition env = do
    expectToken TokenKeywordDef "'def'"
    name <- parseIdentifier
    maybeType <- optional (expectToken TokenColon "':'" *> expressionParser env)
    expectToken TokenEquals "'='"
    bodyTerm <- expressionParser env
    pure (Definition name maybeType bodyTerm)

parseEvaluation :: FixityEnv -> Parser Statement
parseEvaluation env = Evaluation <$> expressionParser env

statementParser :: FixityEnv -> Parser Statement
statementParser env = do
    nextTok <- peekToken
    case nextTok of
        Just TokenKeywordData -> parseDataDeclaration env
        Just TokenKeywordDef -> parseDefinition env
        Just TokenKeywordInfixL -> parseFixityDeclaration env
        Just TokenKeywordInfixR -> parseFixityDeclaration env
        Just TokenKeywordInfix -> parseFixityDeclaration env
        _ -> parseEvaluation env

runCompleteParser :: Parser a -> [PosToken] -> Either ParseError a
runCompleteParser parser tokens =
    case runParser parser tokens of
        Right (result, []) -> Right result
        Right (_, PosToken pos unconsumed : _) -> Left (UnexpectedToken unconsumed pos)
        Left err -> Left err

parseExpression :: Text -> Either ParseError Expression
parseExpression = parseExpressionWith defaultFixityEnv

parseExpressionWith :: FixityEnv -> Text -> Either ParseError Expression
parseExpressionWith env input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    runCompleteParser (expressionParser env) tokens

parseStatement :: Text -> Either ParseError Statement
parseStatement = parseStatementWith defaultFixityEnv

parseStatementWith :: FixityEnv -> Text -> Either ParseError Statement
parseStatementWith env input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    runCompleteParser (statementParser env) tokens

parseProgram :: Text -> Either ParseError [Statement]
parseProgram = parseProgramWith defaultFixityEnv

parseProgramWith :: FixityEnv -> Text -> Either ParseError [Statement]
parseProgramWith env input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    parseAll env tokens
  where
    parseAll :: FixityEnv -> [PosToken] -> Either ParseError [Statement]
    parseAll _ [] = Right []
    parseAll e toks@(PosToken pos t : _) = do
        (stmt, rest) <- runParser (statementParser e) toks
        if length rest == length toks
            then Left (UnexpectedToken t pos)
            else case stmt of
                FixityDeclaration assoc prec ops ->
                    let e' = foldr (\op ex -> Map.insert op (Fixity assoc prec) ex) e ops
                     in (stmt :) <$> parseAll e' rest
                _ -> (stmt :) <$> parseAll e rest

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
