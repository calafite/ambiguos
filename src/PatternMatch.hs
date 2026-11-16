{-# LANGUAGE OverloadedStrings #-}
module PatternMatch (compileClauses) where

import AST (CaseBranch (..), Clause (..), Expression (..), Identifier (..), Pattern (..), PrimType (..), Visibility (..))
import Substitution (substitute)
import qualified Data.Text as Text

-- A small pattern-matrix compiler.  It keeps constructor patterns in `Case`
-- branches and substitutes only variable patterns, leaving the existing case
-- checker and evaluator as the single implementation of matching.
compileClauses :: Maybe Expression -> [Clause] -> Expression
compileClauses _ [] = Hole Nothing
compileClauses maybeType clauses =
    foldr (\(arg, ty) body -> Lambda Explicit arg (Just ty) body)
        (compileMatrix args (map clauseRow clauses))
        (zip args (parameterTypes maybeType (length args)))
  where
    arity = maximum (0 : map (length . clausePatterns) clauses)
    args = [inferNameAt i | i <- [0 .. arity - 1]]
    clauseRow c = (clausePatterns c, clauseBody c)

    parameterTypes (Just ty) n = take n (piDomains ty ++ repeat (PrimType PTInt))
    parameterTypes Nothing n = [inferTypeAt i | i <- [0 .. n - 1]]

    inferTypeAt i
        | any (isListPattern . patternAt i . clausePatterns) clauses =
            Application Explicit (Variable (Identifier "List")) (PrimType PTInt)
        | otherwise = PrimType PTInt

    inferNameAt i = case [v | c <- clauses, PatVar v <- [patternAt i (clausePatterns c)]] of
        v : _ -> v
        [] -> Identifier ("arg" <> Text.pack (show i))

    patternAt i ps = if i < length ps then ps !! i else PatWild
    isListPattern (PatCon n _) = unIdentifier n `elem` ["nil", "cons"]
    isListPattern _ = False

    piDomains (Located _ e) = piDomains e
    piDomains (Pi Implicit _ _ codomain) = piDomains codomain
    piDomains (Pi Instance _ _ codomain) = piDomains codomain
    piDomains (Pi Explicit _ domain codomain) = domain : piDomains codomain
    piDomains _ = []

compileMatrix :: [Identifier] -> [([Pattern], Expression)] -> Expression
compileMatrix _ [] = Hole Nothing
compileMatrix [] ((_, body) : _) = body
compileMatrix (arg : args) rows
    | all (isVariablePattern . headOrWild . fst) rows =
        compileMatrix args [ (drop 1 ps, bind (headOrWild ps) body) | (ps, body) <- rows ]
    | otherwise =
        Case (Variable arg) Nothing (map makeBranch explicitPatterns ++ fallbackBranch)
  where
    headOrWild [] = PatWild
    headOrWild (p : _) = p
    bind (PatVar v) body = substitute v (Variable arg) body
    bind _ body = body

    makeBranch p =
        let childArgs = patternArguments p
            branchRows = [ (rest, body')
                         | (ps, body) <- rows
                         , Just (rest, body') <- [specialize p ps body]
                         ]
         in CaseBranch p (compileMatrix (childArgs ++ args) branchRows)

    fallbackBranch =
        if any (isFallback . headOrWild . fst) rows
            then [CaseBranch PatWild (compileMatrix args [ (drop 1 ps, bind (headOrWild ps) body) | (ps, body) <- rows, isFallback (headOrWild ps) ])]
            else []

    explicitPatterns = unique [p | (ps, _) <- rows, let p = headOrWild ps, not (isFallback p)]

    specialize wanted ps body = case ps of
        [] -> Nothing
        p : rest
            | isFallback p -> Just (rest, bind p body)
            | sameShape wanted p -> Just (patternChildren p ++ rest, body)
            | otherwise -> Nothing

    sameShape (PatCon a _) (PatCon b _) = a == b
    sameShape (PatLit a) (PatLit b) = a == b
    sameShape _ _ = False

    patternChildren (PatCon _ ps) = ps
    patternChildren _ = []

patternArguments :: Pattern -> [Identifier]
patternArguments (PatCon _ ps) = zipWith argumentName [0 :: Int ..] ps
  where
    argumentName i (PatVar v) = v
    argumentName i _ = Identifier ("pat" <> Text.pack (show i))
patternArguments _ = []

isVariablePattern (PatVar _) = True
isVariablePattern PatWild = True
isVariablePattern _ = False

isFallback (PatVar _) = True
isFallback PatWild = True
isFallback _ = False

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x : xs) = x : unique (filter (/= x) xs)
