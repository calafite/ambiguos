module Automata.Types
  ( State (..)
  , Symbol
  , Regex (..)
  , NFA (..)
  , DFA (..)
  ) where

import Data.Map.Strict (Map)
import Data.Set (Set)

newtype State = State
  { unState :: Int
  } deriving (Eq, Ord, Show)

type Symbol = Char

data Regex
  = Empty
  | Epsilon
  | Literal Symbol
  | Concat Regex Regex
  | Union Regex Regex
  | Star Regex
  deriving (Eq, Show)

data NFA = NFA
  { nfaStates      :: Set State
  , nfaAlphabet    :: Set Symbol
  , nfaTransitions :: Map (State, Maybe Symbol) (Set State)
  , nfaStartState  :: State
  , nfaAcceptStates:: Set State
  } deriving (Eq, Show)

data DFA = DFA
  { dfaStates      :: Set State
  , dfaAlphabet    :: Set Symbol
  , dfaTransitions :: Map (State, Symbol) State
  , dfaStartState  :: State
  , dfaAcceptStates:: Set State
  } deriving (Eq, Show)
