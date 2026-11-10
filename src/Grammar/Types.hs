module Grammar.Types (
    NonTerminal (..),
    Symbol (..),
    Production (..),
    CFG (..),
) where

import Data.Set (Set)
import Lexer (Token)

data NonTerminal
    = ProgramNT
    | StatementNT
    | DefinitionNT
    | EvaluationNT
    | ExpressionNT
    | LambdaNT
    | AnnotationNT
    | ArrowNT
    | ApplicationNT
    | AtomNT
    deriving (Eq, Ord, Show)

data Symbol
    = TerminalSymbol Token
    | NonTerminalSymbol NonTerminal
    deriving (Eq, Ord, Show)

data Production = Production
    { productionHead :: NonTerminal
    , productionBody :: [Symbol]
    }
    deriving (Eq, Ord, Show)

data CFG = CFG
    { cfgNonTerminals :: Set NonTerminal
    , cfgTerminals :: Set Token
    , cfgProductions :: [Production]
    , cfgStartSymbol :: NonTerminal
    }
    deriving (Eq, Show)
