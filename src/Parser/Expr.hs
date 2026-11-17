{-# LANGUAGE OverloadedStrings #-}

module Parser.Expr
    ( parseIdentifier
    , parseParenOp
    , desugarList
    , parseLineExpression
    ) where

import AST (Expression (..), Identifier (..), Visibility (..))
import Control.Applicative (Alternative (..))
import Lexer (Token (..), PosToken (..), SourcePos (..))
import Parser.Monad

parseIdentifier :: Parser Identifier
parseIdentifier = parseNamed <|> parseParenOp
  where
    parseNamed = do
        mPt <- peekPosToken
        case mPt of
            Just (PosToken _ (TokenIdentifier ident)) -> consumeToken *> pure ident
            Just (PosToken _ (TokenOperator ident)) -> consumeToken *> pure ident
            Just (PosToken _ (TokenHole Nothing)) -> consumeToken *> pure (Identifier "_")
            Just (PosToken _ (TokenHole (Just (Identifier name)))) ->
                consumeToken *> pure (Identifier ("_" <> name))
            _ -> empty

parseParenOp :: Parser Identifier
parseParenOp = do
    mPt <- peekPosToken
    case mPt of
        Just (PosToken _ TokenLeftParen) -> do
            _ <- consumeToken
            pt <- consumeToken
            case tokenValue pt of
                TokenOperator ident -> expectToken TokenRightParen "')'" *> pure ident
                TokenColon -> expectToken TokenRightParen "')'" *> pure (Identifier ":")
                other -> Parser $ \_ -> Left (ExpectedToken "operator" other (tokenPos pt))
        _ -> empty

desugarList :: [Expression] -> Expression
desugarList [] = Variable (Identifier "[]")
desugarList (x : xs) =
    Application Explicit
        (Application Explicit (Variable (Identifier ":")) x)
        (desugarList xs)

-- | Parse an expression without consuming tokens from a later source line.
-- The expression parser is supplied by the grammar coordinator because the
-- full expression grammar is mutually recursive with declarations.
parseLineExpression :: (FixityEnv -> Parser Expression) -> FixityEnv -> Parser Expression
parseLineExpression expressionParser env = Parser $ \tokens -> case tokens of
    [] -> runParser (expressionParser env) []
    PosToken start _ : _ ->
        let (lineTokens, _) = span (sameLine start) tokens
         in case runParser (expressionParser env) lineTokens of
                Left err -> Left err
                Right (expr, restLine) ->
                    Right (expr, drop (length lineTokens - length restLine) tokens)
  where
    sameLine start (PosToken pos _) = posLine pos == posLine start
