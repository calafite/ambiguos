module Grammar.Types
  ( NonTerminal (..)
  , Symbol (..)
  , Production (..)
  , CFG (..)
  ) where

import Data.Set (Set)
import Lexer (Token)

-- | Non-terminal variables (V) in the Ambiguos Context-Free Grammar
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

-- | A symbol in a production body is either a Terminal (Token) or a Non-Terminal
data Symbol
  = TerminalSymbol Token
  | NonTerminalSymbol NonTerminal
  deriving (Eq, Ord, Show)

-- | A production rule A -> alpha
data Production = Production
  { productionHead :: NonTerminal
  , productionBody :: [Symbol]
  } deriving (Eq, Ord, Show)

-- | Formal 4-tuple G = (V, Sigma, R, S)
data CFG = CFG
  { cfgNonTerminals :: Set NonTerminal
  , cfgTerminals    :: Set Token
  , cfgProductions  :: [Production]
  , cfgStartSymbol  :: NonTerminal
  } deriving (Eq, Show)
