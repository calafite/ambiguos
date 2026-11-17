module Parser
    ( ParseError (..)
    , FixityEnv
    , defaultFixityEnv
    , fixityOf
    , parseExpression
    , parseExpressionWith
    , parseStatement
    , parseStatementWith
    , parseProgram
    , parseProgramWith
    , groupStatements
    , renderParseError
    , renderParseErrorWithSource
    ) where

import Parser.Decl (groupStatements)
import Parser.Grammar
    ( FixityEnv
    , ParseError (..)
    , defaultFixityEnv
    , fixityOf
    , parseExpression
    , parseExpressionWith
    , parseProgram
    , parseProgramWith
    , parseStatement
    , parseStatementWith
    , renderParseError
    , renderParseErrorWithSource
    )
