module Grammar.Analysis (
    firstSets,
    followSets,
) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Grammar.Types
import Lexer (Token)

firstSets :: CFG -> Map NonTerminal (Set (Maybe Token))
firstSets cfg = iterateUntilFixedPoint (step (cfgProductions cfg)) initialMap
  where
    initialMap = Map.fromList [(nt, Set.empty) | nt <- Set.toList (cfgNonTerminals cfg)]

    step prods current =
        foldl
            ( \acc (Production headVar body) ->
                let bodyFirst = deriveSequenceFirst current body
                    existing = Map.findWithDefault Set.empty headVar acc
                 in Map.insert headVar (Set.union existing bodyFirst) acc
            )
            current
            prods

    deriveSequenceFirst _ [] = Set.singleton Nothing
    deriveSequenceFirst currentMap (sym : rest) = case sym of
        TerminalSymbol t -> Set.singleton (Just t)
        NonTerminalSymbol nt ->
            let ntFirst = Map.findWithDefault Set.empty nt currentMap
             in if Set.member Nothing ntFirst
                    then Set.union (Set.delete Nothing ntFirst) (deriveSequenceFirst currentMap rest)
                    else ntFirst

followSets :: CFG -> Map NonTerminal (Set (Maybe Token)) -> Map NonTerminal (Set (Maybe Token))
followSets cfg firsts = iterateUntilFixedPoint (step (cfgProductions cfg)) initialMap
  where
    initialMap =
        Map.fromList
            [ (nt, if nt == cfgStartSymbol cfg then Set.singleton Nothing else Set.empty)
            | nt <- Set.toList (cfgNonTerminals cfg)
            ]

    step prods current =
        foldl (processProduction current) current prods

    processProduction current acc (Production headVar body) =
        let initialTrailer = Map.findWithDefault Set.empty headVar current
         in snd (foldr propagate (initialTrailer, acc) body)

    propagate symbol (trailer, followAcc) = case symbol of
        TerminalSymbol t ->
            (Set.singleton (Just t), followAcc)
        NonTerminalSymbol b ->
            let existingFollow = Map.findWithDefault Set.empty b followAcc
                updatedFollow = Set.union existingFollow trailer
                bFirst = Map.findWithDefault Set.empty b firsts
                newTrailer =
                    if Set.member Nothing bFirst
                        then Set.union (Set.delete Nothing bFirst) trailer
                        else Set.delete Nothing bFirst
             in (newTrailer, Map.insert b updatedFollow followAcc)

iterateUntilFixedPoint :: (Eq a) => (a -> a) -> a -> a
iterateUntilFixedPoint f current =
    let next = f current
     in if next == current then current else iterateUntilFixedPoint f next
