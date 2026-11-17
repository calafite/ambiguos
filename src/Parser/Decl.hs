{-# LANGUAGE OverloadedStrings #-}

module Parser.Decl
    ( groupStatements
    , normalizeTypeSugar
    , parseFixityDeclaration
    ) where

import AST (Associativity (..), Clause (..), Expression (..), Identifier (..), Statement (..), Visibility (..))
import Control.Applicative (Alternative (..), many)
import Lexer (PosToken (..), Token (..))
import Parser.Expr (parseParenOp)
import Parser.Monad

groupStatements :: [Statement] -> [Statement]
groupStatements [] = []
groupStatements (TypeSignature name sig : rest) =
    let (clauses, remaining) = span matching rest
        cs = [c | FunctionClause c <- clauses]
     in if null cs
            then TypeSignature name sig : groupStatements rest
            else FunctionDefinition False name (Just sig) cs : groupStatements remaining
  where
    matching (FunctionClause (Clause n _ _ _)) = n == name
    matching _ = False
groupStatements (FunctionClause c@(Clause name _ _ _) : rest) =
    let (matching, remaining) = span isMatching rest
     in FunctionDefinition False name Nothing (c : [cl | FunctionClause cl <- matching]) : groupStatements remaining
  where
    isMatching (FunctionClause (Clause n _ _ _)) = n == name
    isMatching _ = False
groupStatements (FunctionDefinition partial name mty clauses : rest) =
    let (matching, remaining) = span isMatching rest
     in FunctionDefinition partial name mty (clauses ++ [cl | FunctionClause cl <- matching]) : groupStatements remaining
  where
    isMatching (FunctionClause (Clause n _ _ _)) = n == name
    isMatching _ = False
groupStatements (stmt : rest) = stmt : groupStatements rest

-- | Normalize the surface list type spelling `a : []` used by older
-- declarations into the canonical `List a` application.
normalizeTypeSugar :: Expression -> Expression
normalizeTypeSugar (Located spanInfo expression) = Located spanInfo (normalizeTypeSugar expression)
normalizeTypeSugar (Application Explicit (Application Explicit (Variable (Identifier ":")) element) (Variable (Identifier "[]"))) =
    Application Explicit (Variable (Identifier "List")) (normalizeTypeSugar element)
normalizeTypeSugar (Application visibility function argument) =
    Application visibility (normalizeTypeSugar function) (normalizeTypeSugar argument)
normalizeTypeSugar (Pi visibility name domain codomain) =
    Pi visibility name (normalizeTypeSugar domain) (normalizeTypeSugar codomain)
normalizeTypeSugar (Annotation expression expressionType) =
    Annotation (normalizeTypeSugar expression) (normalizeTypeSugar expressionType)
normalizeTypeSugar expression = expression

parseFixityDeclaration :: FixityEnv -> Parser Statement
parseFixityDeclaration _ = do
    associativity <-
        (AssocLeft <$ expectToken TokenKeywordInfixL "'infixl'")
            <|> (AssocRight <$ expectToken TokenKeywordInfixR "'infixr'")
            <|> (AssocNone <$ expectToken TokenKeywordInfix "'infix'")
    mToken <- peekPosToken
    case mToken of
        Just (PosToken _ (TokenNatural precedence)) -> do
            _ <- consumeToken
            operators <- many parseFixityOperator
            pure (FixityDeclaration associativity (fromInteger precedence) operators)
        _ -> Parser $ \_ -> Left (UnexpectedEndOfInput Nothing)
  where
    parseFixityOperator = parseParenOp <|> do
        mToken <- peekPosToken
        case mToken of
            Just (PosToken _ (TokenOperator operator)) -> consumeToken *> pure operator
            _ -> empty
