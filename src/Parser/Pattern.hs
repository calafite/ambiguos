{-# LANGUAGE OverloadedStrings #-}

module Parser.Pattern
    ( parsePattern
    , parseCasePattern
    ) where

import AST (Identifier (..), Literal (..), Pattern (..))
import Control.Applicative (Alternative (..), many, optional)
import Data.Char (isUpper)
import qualified Data.Text as Text
import Lexer (PosToken (..), Token (..))
import Parser.Expr (parseIdentifier)
import Parser.Monad

parsePattern :: Parser Pattern
parsePattern = parseCasePattern

parseCasePattern :: Parser Pattern
parseCasePattern = do
    mAs <- optional (do
        name <- parseIdentifier
        expectToken TokenAt "'@'"
        pure name)
    left <- parsePatternAtom
    mNext <- peekToken
    case mNext of
        Just TokenColon -> do
            _ <- consumeToken
            right <- parseCasePattern
            pure (case mAs of
                Just asName -> PatAs asName (PatCon (Identifier ":") [left, right])
                Nothing -> PatCon (Identifier ":") [left, right])
        _ -> pure (case mAs of
            Just asName -> PatAs asName left
            Nothing -> left)

parsePatternAtom :: Parser Pattern
parsePatternAtom = parseListPattern <|> do
    mPt <- peekPosToken
    case mPt of
        Just (PosToken _ (TokenNatural n)) -> consumeToken *> pure (PatLit (LitInt (fromInteger n)))
        Just (PosToken _ (TokenFloat n)) -> consumeToken *> pure (PatLit (LitFloat n))
        Just (PosToken _ (TokenChar c)) -> consumeToken *> pure (PatLit (LitChar c))
        Just (PosToken _ (TokenString s)) -> consumeToken *> pure (PatLit (LitString s))
        Just (PosToken _ (TokenHole Nothing)) -> consumeToken *> pure PatWild
        Just (PosToken _ (TokenIdentifier con)) -> do
            _ <- consumeToken
            args <- many parsePatternArgument
            pure (if constructorName con then PatCon con args else PatVar con)
        Just (PosToken _ TokenLeftParen) -> parseTupleOrParenPattern
        _ -> empty
  where
    constructorName (Identifier name) = case Text.uncons name of
        Just (c, _) -> isUpper c
        Nothing -> False

parseTupleOrParenPattern :: Parser Pattern
parseTupleOrParenPattern = do
    expectToken TokenLeftParen "'('"
    first <- parseCasePattern
    mComma <- optional (expectToken TokenComma "','")
    case mComma of
        Just () -> do
            second <- parseCasePattern
            rest <- many (expectToken TokenComma "," *> parseCasePattern)
            expectToken TokenRightParen "')'"
            pure (PatTuple (first : second : rest))
        Nothing -> do
            expectToken TokenRightParen "')'"
            pure first

parsePatternArgument :: Parser Pattern
parsePatternArgument = do
    mPt <- peekPosToken
    case mPt of
        Just (PosToken _ (TokenIdentifier name)) -> consumeToken *> pure (PatVar name)
        Just (PosToken _ (TokenNatural n)) -> consumeToken *> pure (PatLit (LitInt (fromInteger n)))
        Just (PosToken _ (TokenFloat n)) -> consumeToken *> pure (PatLit (LitFloat n))
        Just (PosToken _ (TokenChar c)) -> consumeToken *> pure (PatLit (LitChar c))
        Just (PosToken _ (TokenString s)) -> consumeToken *> pure (PatLit (LitString s))
        Just (PosToken _ (TokenHole Nothing)) -> consumeToken *> pure PatWild
        Just (PosToken _ TokenLeftParen) -> parseCasePattern
        _ -> empty

parseListPattern :: Parser Pattern
parseListPattern = do
    expectToken TokenLeftBracket "'['"
    nextTok <- peekToken
    case nextTok of
        Just TokenRightBracket -> consumeToken *> pure (PatList [])
        _ -> do
            first <- parseCasePattern
            rest <- many (expectToken TokenComma "','" *> parseCasePattern)
            expectToken TokenRightBracket "']'"
            pure (PatList (first : rest))
