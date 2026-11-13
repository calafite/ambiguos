module Automata.NFA (
    compileRegexToNFA,
) where

import Automata.Types
import Control.Monad.State.Strict (get, put, runState)
import qualified Control.Monad.State.Strict as MState
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

type StateSupply = MState.State Int

freshState :: StateSupply Automata.Types.State
freshState = do
    current <- get
    put (current + 1)
    pure (Automata.Types.State current)

data Fragment = Fragment
    { fragStart :: Automata.Types.State
    , fragAccept :: Automata.Types.State
    , fragTransitions :: Map (Automata.Types.State, Maybe Symbol) (Set Automata.Types.State)
    , fragAlphabet :: Set Symbol
    }

insertTransition ::
    Automata.Types.State ->
    Maybe Symbol ->
    Automata.Types.State ->
    Map (Automata.Types.State, Maybe Symbol) (Set Automata.Types.State) ->
    Map (Automata.Types.State, Maybe Symbol) (Set Automata.Types.State)
insertTransition from symbol to transitions =
    Map.insertWith Set.union (from, symbol) (Set.singleton to) transitions

buildFragment :: Regex -> StateSupply Fragment
buildFragment regex = case regex of
    Empty -> do
        s <- freshState
        f <- freshState
        pure (Fragment s f Map.empty Set.empty)
    Epsilon -> do
        s <- freshState
        f <- freshState
        let trans = insertTransition s Nothing f Map.empty
        pure (Fragment s f trans Set.empty)
    Literal symbol -> do
        s <- freshState
        f <- freshState
        let trans = insertTransition s (Just symbol) f Map.empty
        pure (Fragment s f trans (Set.singleton symbol))
    Concat r1 r2 -> do
        f1 <- buildFragment r1
        f2 <- buildFragment r2
        let bridge = insertTransition (fragAccept f1) Nothing (fragStart f2) Map.empty
            combinedTrans = Map.unionsWith Set.union [fragTransitions f1, fragTransitions f2, bridge]
            combinedAlpha = Set.union (fragAlphabet f1) (fragAlphabet f2)
        pure (Fragment (fragStart f1) (fragAccept f2) combinedTrans combinedAlpha)
    Union r1 r2 -> do
        s <- freshState
        f <- freshState
        f1 <- buildFragment r1
        f2 <- buildFragment r2
        let inEps =
                insertTransition s Nothing (fragStart f1) $
                    insertTransition s Nothing (fragStart f2) Map.empty
            outEps =
                insertTransition (fragAccept f1) Nothing f $
                    insertTransition (fragAccept f2) Nothing f Map.empty
            combinedTrans =
                Map.unionsWith
                    Set.union
                    [ fragTransitions f1
                    , fragTransitions f2
                    , inEps
                    , outEps
                    ]
            combinedAlpha = Set.union (fragAlphabet f1) (fragAlphabet f2)
        pure (Fragment s f combinedTrans combinedAlpha)
    Star r -> do
        s <- freshState
        f <- freshState
        inner <- buildFragment r
        let loopEps =
                insertTransition s Nothing (fragStart inner)
                    $ insertTransition s Nothing f
                    $ insertTransition (fragAccept inner) Nothing (fragStart inner)
                    $ insertTransition (fragAccept inner) Nothing f Map.empty
            combinedTrans = Map.unionsWith Set.union [fragTransitions inner, loopEps]
        pure (Fragment s f combinedTrans (fragAlphabet inner))

collectStates ::
    Automata.Types.State ->
    Automata.Types.State ->
    Map (Automata.Types.State, Maybe Symbol) (Set Automata.Types.State) ->
    Set Automata.Types.State
collectStates start accept transitions =
    Set.insert start $ Set.insert accept (foldr collectEdge Set.empty (Map.toList transitions))
  where
    collectEdge ((src, _), dests) acc = Set.insert src (Set.union dests acc)

compileRegexToNFA :: Regex -> NFA
compileRegexToNFA regex =
    let (fragment, _) = runState (buildFragment regex) 0
        allStates = collectStates (fragStart fragment) (fragAccept fragment) (fragTransitions fragment)
     in NFA
            { nfaStates = allStates
            , nfaAlphabet = fragAlphabet fragment
            , nfaTransitions = fragTransitions fragment
            , nfaStartState = fragStart fragment
            , nfaAcceptStates = Set.singleton (fragAccept fragment)
            }
