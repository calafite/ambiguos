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
    groupStatements,
    renderParseError,
    renderParseErrorWithSource,
) where

import AST (CaseBranch (..), ClassMethod (..), Clause (..), Expression (..), Fixity (..), Identifier (..), Literal (..), Pattern (..), PrimOp (..), PrimType (..), RecordField (..), Statement (..), UniverseLevel (..), Associativity (..), Visibility (..))
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
                    pure (Universe (UFixed (fromInteger n)))
                _ -> pure (Universe (UFixed (-1)))
        Just (PosToken _ TokenKeywordId) -> Identity <$ consumeToken
        Just (PosToken _ TokenKeywordRefl) -> Reflexivity <$ consumeToken
        Just (PosToken _ TokenKeywordJ) -> J <$ consumeToken
        Just (PosToken _ TokenKeywordVoid) -> VoidType <$ consumeToken
        Just (PosToken _ TokenKeywordAbort) -> Abort <$ consumeToken
        Just (PosToken _ TokenKeywordNat) -> NatType <$ consumeToken
        Just (PosToken _ TokenKeywordInt) -> PrimType PTInt <$ consumeToken
        Just (PosToken _ TokenKeywordFloat) -> PrimType PTFloat <$ consumeToken
        Just (PosToken _ TokenKeywordChar) -> PrimType PTChar <$ consumeToken
        Just (PosToken _ TokenKeywordString) -> PrimType PTString <$ consumeToken
        Just (PosToken _ TokenKeywordZero) -> Zero <$ consumeToken
        Just (PosToken _ TokenKeywordSucc) -> Succ <$ consumeToken
        Just (PosToken _ TokenKeywordNatRec) -> NatRec <$ consumeToken
        Just (PosToken _ (TokenNatural n)) -> Literal (LitInt n) <$ consumeToken
        Just (PosToken _ (TokenFloat n)) -> Literal (LitFloat n) <$ consumeToken
        Just (PosToken _ (TokenChar c)) -> Literal (LitChar c) <$ consumeToken
        Just (PosToken _ (TokenString s)) -> Literal (LitString s) <$ consumeToken
        Just (PosToken _ (TokenHole mIdent)) -> Hole mIdent <$ consumeToken
        Just (PosToken _ (TokenIdentifier ident)) ->
            parseRecordLiteralAtomic env <|> (Variable ident <$ consumeToken)
        Just (PosToken _ TokenLeftBracket) -> parseListLiteral env
        Just (PosToken _ TokenLeftParen) -> do
            _ <- consumeToken
            nextTok <- peekToken
            case nextTok of
                Just (TokenOperator op) -> do
                    _ <- consumeToken
                    afterOp <- peekToken
                    case afterOp of
                        Just TokenRightParen -> do
                            _ <- consumeToken
                            pure (Variable op)
                        _ | op == Identifier "-" -> do
                            operand <- parsePrefix env
                            expectToken TokenRightParen "')'"
                            let operation = case operand of
                                    Literal (LitFloat _) -> FloatNeg
                                    _ -> IntNeg
                            pure (Application Explicit (PrimOp operation) operand)
                        _ -> Parser $ \_ -> Left (UnexpectedToken (maybe TokenRightParen id afterOp) (SourcePos 0 0))
                _ -> case nextTok of
                    Just TokenRightParen -> consumeToken *> pure (Tuple [])
                    _ -> do
                        expr <- expressionParser env
                        next <- peekToken
                        case next of
                            Just TokenComma -> do
                                _ <- consumeToken
                                second <- expressionParser env
                                rest <- many (expectToken TokenComma "','" *> expressionParser env)
                                expectToken TokenRightParen "')'"
                                pure (Tuple (expr : second : rest))
                            _ -> expectToken TokenRightParen "')'" *> pure expr
        Just (PosToken pos other) -> Parser $ \_ -> Left (UnexpectedToken other pos)
        Nothing -> Parser $ \_ -> Left (UnexpectedEndOfInput Nothing)

parseAppArgument :: FixityEnv -> Parser (Visibility, Expression)
parseAppArgument env = parseInstanceOverride <|> parseImplicitOverride <|> parseExplicitArg env
  where
    parseInstanceOverride = do
        expectToken TokenLeftBrace "'{{'"
        expectToken TokenLeftBrace "'{{'"
        expr <- expressionParser env
        expectToken TokenRightBrace "'}}'"
        expectToken TokenRightBrace "'}}'"
        pure (Instance, expr)
    parseImplicitOverride = do
        expectToken TokenLeftBrace "'{'"
        expr <- expressionParser env
        expectToken TokenRightBrace "'}'"
        pure (Implicit, expr)
    parseExplicitArg e = do
        expr <- parseAtomicExpression e
        pure (Explicit, expr)

parsePrefix :: FixityEnv -> Parser Expression
parsePrefix env = do
    mToken <- peekToken
    case mToken of
        Just (TokenOperator (Identifier "-")) -> do
            _ <- consumeToken
            operand <- parsePrefix env
            let operation = case operand of
                    Literal (LitFloat _) -> FloatNeg
                    _ -> IntNeg
            pure (Application Explicit (PrimOp operation) operand)
        _ -> parseAtomicExpression env

parseRecordLiteralFields :: FixityEnv -> Parser [(Identifier, Expression)]
parseRecordLiteralFields env = do
    first <- parseOne
    rest <- many (expectToken TokenComma "','" *> parseOne)
    pure (first : rest)
  where
    parseOne = do
        name <- parseIdentifier
        expectToken TokenEquals "'='"
        value <- expressionParser env
        pure (name, value)

parseRecordLiteralAtomic :: FixityEnv -> Parser Expression
parseRecordLiteralAtomic env = do
    name <- parseIdentifier
    expectToken TokenLeftBrace "'{'"
    fields <- parseRecordLiteralFields env
    expectToken TokenRightBrace "'}'"
    pure (RecordLiteral name fields)

parseApplication :: FixityEnv -> Parser Expression
parseApplication env = do
    headExpr <- parsePrefix env
    argExprs <- many (parseAppArgument env)
    pure (foldl (\acc (vis, arg) -> Application vis acc arg) headExpr argExprs)

parseDependentArrow :: FixityEnv -> Parser Expression
parseDependentArrow env = parseExplicit <|> parseInstanceTyped <|> parseInstanceUnnamed <|> parseImplicit
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

    parseInstanceTyped = do
        expectToken TokenLeftBrace "'{{'"
        expectToken TokenLeftBrace "'{{'"
        parameterNames <- some parseIdentifier
        expectToken TokenColon "':'"
        domainType <- expressionParser env
        expectToken TokenRightBrace "'}}'"
        expectToken TokenRightBrace "'}}'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser env
        pure (foldr (\name acc -> Pi Instance name domainType acc) codomainType parameterNames)

    parseInstanceUnnamed = do
        expectToken TokenLeftBrace "'{{'"
        expectToken TokenLeftBrace "'{{'"
        constraintType <- expressionParser env
        expectToken TokenRightBrace "'}}'"
        expectToken TokenRightBrace "'}}'"
        expectToken TokenArrow "'->'"
        codomainType <- expressionParser env
        pure (Pi Instance (Identifier "_") constraintType codomainType)

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

-- | Postfix projection parser: parses `expr.field` chains at atomic precedence.
parsePostfix :: FixityEnv -> Parser Expression
parsePostfix env = do
    left <- parseApplication env
    postfixLoop left
  where
    postfixLoop left = do
        mDot <- peekToken
        case mDot of
            Just TokenDot -> do
                _ <- consumeToken
                field <- parseIdentifier
                postfixLoop (Projection left field)
            _ -> pure left

-- | Precedence-climbing parser for infix operators.
-- `minPrec` is the minimum precedence an operator must have to be consumed.
parseInfix :: FixityEnv -> Int -> Parser Expression
parseInfix env minPrec = do
    left <- parsePostfix env
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
    | TupleParameters [Identifier]

parseParameterGroup :: FixityEnv -> Parser ParameterGroup
parseParameterGroup env = parseTypedInstance <|> parseInstanceNames <|> parseTupleParameters <|> parseTypedParen <|> parseTypedBrace <|> parseSimple
  where
    parseTypedInstance = do
        expectToken TokenLeftBrace "'{{'"
        expectToken TokenLeftBrace "'{{'"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser env
        expectToken TokenRightBrace "'}}'"
        expectToken TokenRightBrace "'}}'"
        pure (TypedParameters Instance names paramType)

    parseInstanceNames = do
        expectToken TokenLeftBrace "'{{'"
        expectToken TokenLeftBrace "'{{'"
        names <- some parseIdentifier
        expectToken TokenRightBrace "'}}'"
        expectToken TokenRightBrace "'}}'"
        pure (TypedParameters Instance names (Variable (Identifier "_")))

    parseTypedParen = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        paramType <- expressionParser env
        expectToken TokenRightParen "')'"
        pure (TypedParameters Explicit names paramType)

    parseTupleParameters = do
        expectToken TokenLeftParen "'('"
        first <- parseIdentifier
        _ <- expectToken TokenComma "','"
        rest <- some (parseIdentifier <* optional (expectToken TokenComma "','"))
        expectToken TokenRightParen "')'"
        pure (TupleParameters (first : rest))

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
    expandGroup (TupleParameters names) acc =
        let binder = Identifier "tupleParam"
            pattern = PatTuple (map PatVar names)
         in Lambda Explicit binder Nothing (PatternCase (Variable binder) Nothing [(pattern, acc)])

parseLet :: FixityEnv -> Parser Expression
parseLet env = do
    expectToken TokenKeywordLet "'let'"
    tupleStart <- optional (expectToken TokenLeftParen "'('")
    case tupleStart of
        Just _ -> do
            first <- parseIdentifier
            _ <- expectToken TokenComma "','"
            rest <- some (parseIdentifier <* optional (expectToken TokenComma "','"))
            expectToken TokenRightParen "')'"
            expectToken TokenEquals "'='"
            valExpr <- expressionParser env
            expectToken TokenKeywordIn "'in'"
            bodyExpr <- expressionParser env
            pure (PatternCase valExpr Nothing [(PatTuple (map PatVar (first : rest)), bodyExpr)])
        Nothing -> do
            name <- parseIdentifier
            maybeType <- optional (expectToken TokenColon "':'" *> expressionParser env)
            expectToken TokenEquals "'='"
            valExpr <- expressionParser env
            expectToken TokenKeywordIn "'in'"
            bodyExpr <- expressionParser env
            pure (Let name maybeType valExpr bodyExpr)

parsePattern :: Parser Pattern
parsePattern = parseParen <|> parseWild <|> parseNatural <|> parseNamed
  where
    parseParen = do
        expectToken TokenLeftParen "'('"
        next <- peekToken
        case next of
            Just TokenRightParen -> consumeToken *> pure (PatTuple [])
            _ -> do
                p <- parsePattern
                next' <- peekToken
                case next' of
                    Just TokenComma -> do
                        _ <- consumeToken
                        p2 <- parsePattern
                        rest <- many (expectToken TokenComma "','" *> parsePattern)
                        expectToken TokenRightParen "')'"
                        pure (PatTuple (p : p2 : rest))
                    _ -> expectToken TokenRightParen "')'" *> pure p
    parseWild = do
        expectToken (TokenHole Nothing) "'_'"
        pure PatWild
    parseNatural = do
        pt <- consumeToken
        case tokenValue pt of
            TokenNatural n -> pure (PatLit (LitNat n))
            _ -> empty
    parseNamed = do
        name <- parseIdentifier
        args <- many parsePatternArg
        -- In a case-clause head an identifier denotes a constructor; variable
        -- binders are represented by wildcard/nested argument positions.
        pure (PatCon name args)
    parsePatternArg = do
        next <- peekToken
        case next of
            Just (TokenIdentifier _) -> do
                name <- parseIdentifier
                let raw = unIdentifier name
                pure (if raw `elem` ["nil", "true", "false", "pair", "sigma", "nothing", "just", "left", "right", "dependentPair"] then PatCon name [] else PatVar name)
            Just TokenKeywordZero -> PatCon (Identifier "zero") [] <$ consumeToken
            Just TokenKeywordSucc -> PatCon (Identifier "successor") [] <$ consumeToken
            Just (TokenNatural _) -> parsePattern
            Just (TokenHole Nothing) -> PatWild <$ consumeToken
            Just TokenLeftParen -> parsePattern
            _ -> empty

parsePatternBranch :: FixityEnv -> Parser (Pattern, Expression)
parsePatternBranch env = do
    pattern <- parsePattern
    expectToken TokenArrow "'->'"
    body <- expressionParser env
    pure (pattern, body)

-- Patterns used by the ordinary `case` form.  A leading identifier is kept as
-- a constructor candidate; the type checker can reinterpret a nullary name as
-- a variable when the scrutinee has a primitive type.
parseCasePattern :: Parser Pattern
parseCasePattern = do
    mPt <- peekPosToken
    case mPt of
        Just (PosToken _ (TokenNatural n)) -> consumeToken *> pure (PatLit (LitNat n))
        Just (PosToken _ (TokenFloat n)) -> consumeToken *> pure (PatLit (LitFloat n))
        Just (PosToken _ (TokenChar c)) -> consumeToken *> pure (PatLit (LitChar c))
        Just (PosToken _ (TokenString s)) -> consumeToken *> pure (PatLit (LitString s))
        Just (PosToken _ (TokenHole Nothing)) -> consumeToken *> pure PatWild
        Just (PosToken _ TokenKeywordZero) -> consumeToken *> pure (PatCon (Identifier "zero") [])
        Just (PosToken _ TokenKeywordSucc) -> do
            _ <- consumeToken
            args <- many parseAtomicCasePattern
            pure (PatCon (Identifier "successor") args)
        Just (PosToken _ (TokenIdentifier con)) -> do
            _ <- consumeToken
            args <- many parseAtomicCasePattern
            pure (PatCon con args)
        Just (PosToken _ TokenLeftParen) -> do
            expectToken TokenLeftParen "'('"
            p <- parseCasePattern
            expectToken TokenRightParen "')'"
            pure p
        _ -> empty
  where
    parseAtomicCasePattern = do
        mPt <- peekPosToken
        case mPt of
            Just (PosToken _ (TokenIdentifier name)) -> consumeToken *> pure (PatVar name)
            Just (PosToken _ (TokenNatural n)) -> consumeToken *> pure (PatLit (LitNat n))
            Just (PosToken _ (TokenFloat n)) -> consumeToken *> pure (PatLit (LitFloat n))
            Just (PosToken _ (TokenChar c)) -> consumeToken *> pure (PatLit (LitChar c))
            Just (PosToken _ (TokenString s)) -> consumeToken *> pure (PatLit (LitString s))
            Just (PosToken _ (TokenHole Nothing)) -> consumeToken *> pure PatWild
            Just (PosToken _ TokenKeywordZero) -> consumeToken *> pure (PatCon (Identifier "zero") [])
            Just (PosToken _ TokenKeywordSucc) -> consumeToken *> pure (PatCon (Identifier "successor") [])
            Just (PosToken _ TokenLeftParen) -> parseCasePattern
            _ -> empty

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
    pure (Case target mMotive [CaseBranch pat body | (pat, body) <- branches])
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
        bs <- many (parseCasePatternBranch env <* optional (expectToken TokenSemicolon "';'"))
        expectToken TokenRightBrace "'}'"
        pure bs
    parsePiped = do
        _ <- optional (expectToken TokenPipe "'|'")
        b1 <- parseCasePatternBranch env
        bs <- many (expectToken TokenPipe "'|'" *> parseCasePatternBranch env)
        pure (b1 : bs)
    parseCasePatternBranch env = do
        pat <- parseCasePattern
        expectToken TokenArrow "'->'"
        body <- expressionParser env
        pure (pat, body)

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

parseRecordField :: FixityEnv -> Parser RecordField
parseRecordField env = do
    name <- parseIdentifier
    expectToken TokenColon "':'"
    ty <- expressionParser env
    pure (RecordField name ty)

parseRecordDeclaration :: FixityEnv -> Parser Statement
parseRecordDeclaration env = do
    expectToken TokenKeywordRecord "'record'"
    name <- parseIdentifier
    paramGroups <- many (parseDataParameter env)
    expectToken TokenColon "':'"
    univ <- expressionParser env
    expectToken TokenKeywordWhere "'where'"
    expectToken TokenLeftBrace "'{'"
    mExplicitConstructor <- optional parseConstructorClause
    fields <- case mExplicitConstructor of
        Just _ -> optional (expectToken TokenSemicolon "';'") *> parseRecordFields env
        Nothing -> parseRecordFields env
    expectToken TokenRightBrace "'}'"
    let allParams = concat paramGroups
        conName = maybe (Identifier ("mk" <> unIdentifier name)) id mExplicitConstructor
    pure (RecordDeclaration name allParams univ fields (Just conName))
  where
    parseConstructorClause = do
        ident <- parseIdentifier
        if ident == Identifier "constructor"
            then parseIdentifier
            else empty

    parseRecordFields :: FixityEnv -> Parser [RecordField]
    parseRecordFields e = do
        f <- parseRecordField e
        rest <- many (expectToken TokenSemicolon "';'" *> parseRecordField e)
        pure (f : rest)

parseClassDeclaration :: FixityEnv -> Parser Statement
parseClassDeclaration env = parseLegacy <|> parseDetailed
  where
    parseDetailed = do
        expectToken TokenKeywordClass "'class'"
        name <- parseIdentifier
        params <- many (parseDataParameter env)
        expectToken TokenKeywordWhere "'where'"
        expectToken TokenLeftBrace "'{'"
        methods <- parseMethods
        expectToken TokenRightBrace "'}'"
        pure (ClassDeclarationDetailed name (concat params) methods)
    parseMethods = do
        method <- do
            methodName <- parseIdentifier
            expectToken TokenColon "':'"
            methodType <- expressionParser env
            defaultBody <- optional (expectToken TokenEquals "'='" *> expressionParser env)
            pure (ClassMethod methodName methodType defaultBody)
        rest <- many (optional (expectToken TokenSemicolon "';'") *> parseMethods)
        pure (method : concat rest)
    parseLegacy = do
        expectToken TokenKeywordClass "'class'"
        name <- parseIdentifier
        params <- many (parseDataParameter env)
        expectToken TokenKeywordWhere "'where'"
        expectToken TokenLeftBrace "'{'"
        fields <- parseClassFields
        expectToken TokenRightBrace "'}'"
        pure (ClassDeclaration name (concat params) (Universe (UFixed (-1))) fields)
    parseClassFields = do
        f <- parseRecordField env
        rest <- many (optional (expectToken TokenSemicolon "';'") *> parseRecordField env)
        pure (f : rest)

parseInstanceDeclaration :: FixityEnv -> Parser Statement
parseInstanceDeclaration env = parseDetailed <|> parseLegacy
  where
    parseDetailed = do
        expectToken TokenKeywordInstance "'instance'"
        params <- many (parseDataParameter env)
        expectToken TokenArrow "'->'"
        className <- parseIdentifier
        headType <- parseInfix env 0
        expectToken TokenKeywordWhere "'where'"
        expectToken TokenLeftBrace "'{'"
        clauses <- parseClauses
        expectToken TokenRightBrace "'}'"
        pure (InstanceDeclarationDetailed className (concat params) headType clauses)
    parseClauses = do
        _ <- optional (expectToken TokenPipe "'|'" )
        first <- parseClause
        rest <- many (expectToken TokenPipe "'|'" *> parseClause)
        pure (first : rest)
    parseClause = do
        patterns <- many (normalize <$> parseCasePattern)
        expectToken TokenEquals "'='"
        body <- expressionParser env
        pure (Clause (Identifier "_") patterns body)
    normalize (PatCon n [])
        | unIdentifier n `notElem` ["nil", "true", "false", "zero", "successor", "nothing"] = PatVar n
    normalize (PatCon n ps) = PatCon n (map normalize ps)
    normalize (PatTuple ps) = PatTuple (map normalize ps)
    normalize p = p
    parseLegacy = do
        expectToken TokenKeywordInstance "'instance'"
        className <- parseIdentifier
        headType <- parseInfix env 0
        expectToken TokenKeywordWhere "'where'"
        expectToken TokenLeftBrace "'{'"
        fields <- parseInstanceFields
        expectToken TokenRightBrace "'}'"
        pure (InstanceDeclaration className headType fields)
    parseInstanceFields = do
        f <- parseOne
        rest <- many (optional (expectToken TokenSemicolon "';'") *> parseOne)
        pure (f : rest)
    parseOne = do
        field <- parseIdentifier
        expectToken TokenEquals "'='"
        value <- expressionParser env
        pure (field, value)

parseModulePath :: Parser [Identifier]
parseModulePath = do
    first <- parseIdentifier
    rest <- many (expectToken TokenDot "'.'" *> parseIdentifier)
    pure (first : rest)

parseModuleHeader :: Parser Statement
parseModuleHeader = do
    expectToken TokenKeywordModule "'module'"
    ModuleHeader <$> parseModulePath

parseImportStatement :: Parser Statement
parseImportStatement = do
    expectToken TokenKeywordImport "'import'"
    qualifiedImport <- (True <$ expectToken TokenKeywordQualified "'qualified'") <|> pure False
    path <- parseModulePath
    alias <- optional (expectToken TokenKeywordAs "'as'" *> parseIdentifier)
    importList <- optional (parseNamesInParens)
    pure (ImportStmt qualifiedImport path importList alias)
  where
    parseNamesInParens = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenRightParen "')'"
        pure names

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

parseFunctionEquation :: FixityEnv -> Parser Statement
parseFunctionEquation env = do
    name <- parseIdentifier
    next <- peekToken
    case next of
        Just TokenColon -> do
            _ <- consumeToken
            TypeSignature name <$> parseLineExpression env
        _ -> do
            (patterns, mTypedTypes) <- parseLhs [] []
            mResultType <- optional (expectToken TokenColon "':'" *> expressionParser env)
            expectToken TokenEquals "'='"
            body <- parseLineExpression env
            let declaredType = case mResultType of
                    Nothing -> Nothing
                    Just result -> Just (foldr (\(n, ty) rest -> Pi Explicit n ty rest) result mTypedTypes)
                clause = Clause name patterns body
            pure (case declaredType of
                Just ty -> FunctionDefinition name (Just ty) [clause]
                Nothing -> FunctionClause clause)
  where
    parseLhs pats typed = do
        next <- peekToken
        case next of
            Just TokenEquals -> pure (pats, typed)
            Just TokenColon -> pure (pats, typed)
            _ -> do
                (newPats, newTyped) <- parseTypedGroup <|> do
                    p <- equationPattern
                    pure ([p], [])
                parseLhs (pats ++ newPats) (typed ++ newTyped)
    equationPattern = normalize <$> parseEquationPattern
    parseEquationPattern = do
        next <- peekPosToken
        case next of
            Just (PosToken _ (TokenIdentifier n)) -> consumeToken *> pure (identifierPattern n)
            Just (PosToken _ (TokenHole Nothing)) -> consumeToken *> pure PatWild
            Just (PosToken _ TokenKeywordZero) -> consumeToken *> pure (PatCon (Identifier "zero") [])
            Just (PosToken _ TokenKeywordSucc) -> consumeToken *> pure (PatCon (Identifier "successor") [])
            Just (PosToken _ TokenLeftParen) -> parseCasePattern
            _ -> parseCasePattern
    normalize (PatCon n [])
        | unIdentifier n `notElem` ["nil", "true", "false", "zero", "successor", "nothing"] = PatVar n
    normalize p = p
    identifierPattern n
        | unIdentifier n `elem` ["nil", "true", "false", "zero", "successor", "nothing"] = PatCon n []
        | otherwise = PatVar n
    parseTypedGroup = do
        expectToken TokenLeftParen "'('"
        names <- some parseIdentifier
        expectToken TokenColon "':'"
        ty <- expressionParser env
        expectToken TokenRightParen "')'"
        pure ([PatVar n | n <- names], [(n, ty) | n <- names])

parseLineExpression :: FixityEnv -> Parser Expression
parseLineExpression env = Parser $ \tokens -> case tokens of
    [] -> runParser (expressionParser env) []
    PosToken start _ : _ ->
        let (lineTokens, _) = span (sameLine start) tokens
         in case runParser (expressionParser env) lineTokens of
                Left err -> Left err
                Right (expr, restLine) ->
                    Right (expr, drop (length lineTokens - length restLine) tokens)
  where
    sameLine start (PosToken pos _) = posLine pos == posLine start

parseEvaluation :: FixityEnv -> Parser Statement
parseEvaluation env = Evaluation <$> expressionParser env

statementParser :: FixityEnv -> Parser Statement
statementParser env = do
    nextTok <- peekToken
    case nextTok of
        Just TokenKeywordModule -> parseModuleHeader
        Just TokenKeywordImport -> parseImportStatement
        Just TokenKeywordClass -> parseClassDeclaration env
        Just TokenKeywordInstance -> parseInstanceDeclaration env
        Just TokenKeywordData -> parseDataDeclaration env
        Just TokenKeywordRecord -> parseRecordDeclaration env
        Just TokenKeywordDef -> parseDefinition env
        Just TokenKeywordInfixL -> parseFixityDeclaration env
        Just TokenKeywordInfixR -> parseFixityDeclaration env
        Just TokenKeywordInfix -> parseFixityDeclaration env
        Just (TokenIdentifier _) -> parseFunctionEquation env <|> parseEvaluation env
        Just (TokenOperator _) -> parseFunctionEquation env <|> parseEvaluation env
        Just TokenLeftParen -> parseFunctionEquation env <|> parseEvaluation env
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
    statements <- parseProgramWith env input
    case statements of
        [statement] -> Right statement
        _ -> Left (UnexpectedEndOfInput Nothing)

parseProgram :: Text -> Either ParseError [Statement]
parseProgram = parseProgramWith defaultFixityEnv

parseProgramWith :: FixityEnv -> Text -> Either ParseError [Statement]
parseProgramWith env input = do
    tokens <- case tokenize input of
        Left lexErr -> Left (ErrorLexical lexErr)
        Right toks -> Right toks
    groupStatements <$> parseAll env tokens
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

groupStatements :: [Statement] -> [Statement]
groupStatements [] = []
groupStatements (TypeSignature name sig : rest) =
    let (clauses, remaining) = span matching rest
        cs = [c | FunctionClause c <- clauses]
     in if null cs
            then TypeSignature name sig : groupStatements rest
            else FunctionDefinition name (Just sig) cs : groupStatements remaining
  where
    matching (FunctionClause (Clause n _ _)) = n == name
    matching _ = False
groupStatements (FunctionClause c@(Clause name _ _) : rest) =
    let (matching, remaining) = span isMatching rest
     in FunctionDefinition name Nothing (c : [cl | FunctionClause cl <- matching]) : groupStatements remaining
  where
    isMatching (FunctionClause (Clause n _ _)) = n == name
    isMatching _ = False
groupStatements (FunctionDefinition name mty clauses : rest) =
    let (matching, remaining) = span isMatching rest
     in FunctionDefinition name mty (clauses ++ [cl | FunctionClause cl <- matching]) : groupStatements remaining
  where
    isMatching (FunctionClause (Clause n _ _)) = n == name
    isMatching _ = False
groupStatements (stmt : rest) = stmt : groupStatements rest

renderParseError :: ParseError -> Text
renderParseError = renderParseErrorWithSource Nothing Nothing

renderParseErrorWithSource :: Maybe FilePath -> Maybe Text -> ParseError -> Text
renderParseErrorWithSource mFile mSource err = case err of
    ErrorLexical lexErr -> case mSource of
        Just src ->
            let pos = case lexErr of
                    UnexpectedCharacter p _ -> p
                    UnterminatedBlockComment p -> p
                    UnterminatedString p -> p
                    InvalidEscape p _ -> p
                    InvalidCharLiteral p -> p
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
