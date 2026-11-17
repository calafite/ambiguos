{-# LANGUAGE OverloadedStrings #-}

module Parser.Monad
    ( FixityEnv
    , defaultFixityEnv
    , fixityOf
    , ParseError (..)
    , Parser (..)
    , withSpan
    , peekToken
    , peekPosToken
    , consumeToken
    , expectToken
    ) where

import AST (Expression (..), Fixity (..), Identifier (..), Associativity (..))
import Control.Applicative (Alternative (..))
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Diagnostics (SourceSpan (..))
import Lexer (LexError (..), PosToken (..), SourcePos (..), Token (..))

type FixityEnv = Map.Map Identifier Fixity

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
