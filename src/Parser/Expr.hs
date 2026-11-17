module Parser.Expr
    ( parseLineExpression
    ) where

import AST (Expression)
import Parser.Monad
import Lexer (PosToken (..), SourcePos (..))

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
