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
import Parser.Monad

parsePattern :: Parser Pattern
parsePattern = parseCasePattern

parseCasePattern :: Parser Pattern
parseCasePattern = do
    left <- parsePatternAtom
    hasCons <- optional (expectToken TokenColon "':'")
    case hasCons of
        Nothing -> pure left
        Just () -> do
            right <- parseCasePattern
            pure (PatCon (Identifier ":") [left, right])

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
        Just (PosToken _ TokenLeftParen) -> do
            expectToken TokenLeftParen "'('"
            p <- parseCasePattern
            expectToken TokenRightParen "')'"
            pure p
        _ -> empty
  where
    constructorName (Identifier name) = case Text.uncons name of
        Just (c, _) -> isUpper c
        Nothing -> False

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
