module Automata.Types
  ( State (..)
  , Symbol
  , Regex (..)
  , NFA (..)
  , DFA (..)
  , matchAny
  , literalString
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

matchAny :: [Symbol] -> Regex
matchAny [] = Empty
matchAny [c] = Literal c
matchAny (c : cs) = Union (Literal c) (matchAny cs)

literalString :: String -> Regex
literalString [] = Epsilon
literalString [c] = Literal c
literalString (c : cs) = Concat (Literal c) (literalString cs)

data NFA = NFA
  { nfaStates       :: Set State
  , nfaAlphabet    :: Set Symbol
  , nfaTransitions :: Map (State, Maybe Symbol) (Set State)
  , nfaStartState  :: State
  , nfaAcceptStates:: Set State
  } deriving (Eq, Show)

data DFA = DFA
  { dfaStates       :: Set State
  , dfaAlphabet    :: Set Symbol
  , dfaTransitions :: Map (State, Symbol) State
  , dfaStartState  :: State
  , dfaAcceptStates:: Set State
  } deriving (Eq, Show)
