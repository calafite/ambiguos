{-# LANGUAGE OverloadedStrings #-}

module Automata.DFA
  ( compileNFAToDFA
  , simulateDFA
  , matchPrefixDFA
  , exportDFAToJSON
  ) where

import Automata.Types
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)

epsilonClosure :: Map (State, Maybe Symbol) (Set State) -> Set State -> Set State
epsilonClosure transitions initialStates = expand initialStates (Set.toList initialStates)
  where
    expand current [] = current
    expand current (x : xs) =
      let epsNeighbors = Map.findWithDefault Set.empty (x, Nothing) transitions
          unseen = Set.difference epsNeighbors current
      in expand (Set.union current unseen) (Set.toList unseen ++ xs)

move :: Map (State, Maybe Symbol) (Set State) -> Set State -> Symbol -> Set State
move transitions states symbol =
  Set.unions [ Map.findWithDefault Set.empty (s, Just symbol) transitions | s <- Set.toList states ]

compileNFAToDFA :: NFA -> DFA
compileNFAToDFA nfa =
  buildDFA
    [startSet]
    (Set.singleton startSet)
    Map.empty
    (Map.singleton startSet (State 0))
    1
  where
    startSet = epsilonClosure (nfaTransitions nfa) (Set.singleton (nfaStartState nfa))
    alphabetList = Set.toList (nfaAlphabet nfa)

    buildDFA [] _ visitedTransitions stateMapping _ =
      let dfaTrans = Map.mapKeys (\(subset, sym) -> (stateMapping Map.! subset, sym))
                                 (Map.map (stateMapping Map.!) visitedTransitions)
          allDfaStates = Set.fromList (Map.elems stateMapping)
          acceptDfaStates = Set.fromList
            [ stateMapping Map.! subset
            | subset <- Map.keys stateMapping
            , not (Set.disjoint subset (nfaAcceptStates nfa))
            ]
      in DFA
          { dfaStates       = allDfaStates
          , dfaAlphabet     = nfaAlphabet nfa
          , dfaTransitions  = dfaTrans
          , dfaStartState   = State 0
          , dfaAcceptStates = acceptDfaStates
          }

    buildDFA (currentSubset : workList) seenSubsets accumulatedTransitions stateMapping nextStateIndex =
      let transitionsForSubset =
            [ (symbol, nextSubset)
            | symbol <- alphabetList
            , let nextSubset = epsilonClosure (nfaTransitions nfa) (move (nfaTransitions nfa) currentSubset symbol)
            , not (Set.null nextSubset)
            ]
          newSubsets = [ next | (_, next) <- transitionsForSubset, Set.notMember next seenSubsets ]
          (updatedMapping, updatedIndex) =
            foldr (\sub (mapping, idx) -> (Map.insert sub (State idx) mapping, idx + 1))
                  (stateMapping, nextStateIndex)
                  newSubsets
          newTransitions = foldr (\(sym, next) acc -> Map.insert (currentSubset, sym) next acc)
                                 accumulatedTransitions
                                 transitionsForSubset
          updatedSeen = Set.union seenSubsets (Set.fromList newSubsets)
      in buildDFA
          (workList ++ newSubsets)
          updatedSeen
          newTransitions
          updatedMapping
          updatedIndex

simulateDFA :: DFA -> String -> Bool
simulateDFA dfa inputString =
  let finalState = foldl step (Just (dfaStartState dfa)) inputString
  in case finalState of
       Just st -> Set.member st (dfaAcceptStates dfa)
       Nothing -> False
  where
    step Nothing _ = Nothing
    step (Just current) symbol = Map.lookup (current, symbol) (dfaTransitions dfa)

matchPrefixDFA :: DFA -> String -> Maybe (String, String)
matchPrefixDFA dfa input = go (dfaStartState dfa) input [] Nothing
  where
    go currentState remaining currentMatched lastAccept =
      let updatedAccept =
            if Set.member currentState (dfaAcceptStates dfa)
              then Just (reverse currentMatched, remaining)
              else lastAccept
      in case remaining of
           [] -> updatedAccept
           (c : cs) ->
             case Map.lookup (currentState, c) (dfaTransitions dfa) of
               Just nextState ->
                 go nextState cs (c : currentMatched) updatedAccept
               Nothing ->
                 updatedAccept

exportDFAToJSON :: DFA -> Text
exportDFAToJSON dfa =
  "{\n" <> Text.intercalate ",\n" (map formatState (Set.toList (dfaStates dfa))) <> "\n}"
  where
    formatState (State sId) =
      let transitions =
            [ "\"" <> Text.singleton sym <> "\" : \"q" <> Text.pack (show (unState target)) <> "\""
            | sym <- Set.toList (dfaAlphabet dfa)
            , Just target <- [Map.lookup (State sId, sym) (dfaTransitions dfa)]
            ]
      in "  \"q" <> Text.pack (show sId) <> "\" : { " <> Text.intercalate ", " transitions <> " }"
