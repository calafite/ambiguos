{-# LANGUAGE OverloadedStrings #-}
module PatternMatch (compileClauses) where

import AST (CaseBranch (..), Clause (..), Expression (..), GuardedRhs (..), Identifier (..), Literal (..), Pattern (..), PrimType (..), Visibility (..))
import Substitution (substitute)
import qualified Data.Text as Text

-- | Clause body extraction: take the first RHS body (guards handled by type checker).
clauseBody :: Clause -> Expression
clauseBody = guardedRhsBody . head . clauseRhss

compileClauses :: Maybe Expression -> [Clause] -> Expression
compileClauses _ [] = Hole Nothing
compileClauses maybeType clauses =
    foldr (\(visibility, name, ty) body -> Lambda visibility name (Just ty) body)
        (compileMatrix args (map clauseRow clauses))
        (clauseBinders maybeType args)
  where
    arity = maximum (0 : map (length . clausePats) clauses)
    args = [inferNameAt i | i <- [0 .. arity - 1]]
    clauseRow c = (map normalizePattern (clausePats c), clauseBody c)

    piBinders (Located _ e) = piBinders e
    piBinders (Pi visibility parameter domain codomain) = (visibility, parameter, domain) : piBinders codomain
    piBinders _ = []

    clauseBinders (Just ty) explicitArgs = assignExplicit explicitArgs (piBinders ty)
    clauseBinders Nothing explicitArgs = [(Explicit, arg, inferTypeAt i) | (i, arg) <- zip [0 ..] explicitArgs]

    assignExplicit remaining [] =
        [(Explicit, arg, PrimType PTInt) | arg <- remaining]
    assignExplicit remaining ((visibility, name, domain) : rest)
        | visibility == Explicit =
            case remaining of
                arg : more -> (Explicit, arg, domain) : assignExplicit more rest
                [] -> []
        | otherwise = (visibility, name, domain) : assignExplicit remaining rest

    inferTypeAt i
        | any (isListPattern . patternAt i . clausePats) clauses =
            Application Explicit (Variable (Identifier "List")) (PrimType PTInt)
        | otherwise = PrimType PTInt

    inferNameAt i = case [v | c <- clauses, PatVar v <- [patternAt i (clausePats c)]] of
        v : _ -> v
        [] -> Identifier ("arg" <> Text.pack (show i))

    patternAt i ps = if i < length ps then ps !! i else PatWild
    isListPattern (PatList _) = True
    isListPattern _ = False

    normalizePattern (PatList []) = PatCon (Identifier "[]") []
    normalizePattern (PatList (p : ps)) = PatCon (Identifier ":") [normalizePattern p, normalizePattern (PatList ps)]
    normalizePattern (PatTuple []) = PatCon (Identifier "()") []
    normalizePattern (PatTuple [p]) = normalizePattern p
    normalizePattern (PatTuple (p : ps)) = PatCon (Identifier "Pair") [normalizePattern p, normalizePattern (PatTuple ps)]
    normalizePattern (PatAs n p) = PatAs n (normalizePattern p)
    normalizePattern (PatLit (LitString s)) = stringPattern s
    normalizePattern (PatCon n ps) = PatCon n (map normalizePattern ps)
    normalizePattern p = p

    stringPattern s = case Text.uncons s of
        Nothing -> PatCon (Identifier "[]") []
        Just (c, rest) -> PatCon (Identifier ":") [PatLit (LitChar c), stringPattern rest]

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
        let childArgs = constructorArguments p
            pat = branchShape p childArgs
            branchRows = [ (rest, body')
                         | (ps, body) <- rows
                         , Just (rest, body') <- [specialize p ps body arg]
                         ]
         in CaseBranch pat [GuardedRhs [] (compileMatrix (childArgs ++ args) branchRows)] []

    fallbackBranch =
        if any (isFallback . headOrWild . fst) rows
            then [CaseBranch PatWild [GuardedRhs [] (compileMatrix args [ (drop 1 ps, bindAt arg (headOrWild ps) body) | (ps, body) <- rows, isFallback (headOrWild ps) ])] []]
            else []

    explicitPatterns = unique [shape p | (ps, _) <- rows, let p = headOrWild ps, not (isFallback p)]

    shape (PatCon con ps) = PatCon con (replicate (length ps) PatWild)
    shape p = p

    specialize wanted ps body scrutinee = case ps of
        [] -> Nothing
        p : rest
            | isFallback p -> Just (rest, bindAt scrutinee p body)
            | sameShape wanted p -> Just (patternChildren p ++ rest, body)
            | otherwise -> Nothing

    sameShape (PatCon a _) (PatCon b _) = a == b
    sameShape (PatLit a) (PatLit b) = a == b
    sameShape _ _ = False

    patternChildren (PatCon _ ps) = ps
    patternChildren _ = []

    constructorArguments (PatCon _ ps) = zipWith argumentName [0 :: Int ..] ps
    constructorArguments _ = []
    argumentName _ (PatVar v) = v
    argumentName i _ = Identifier ("pat" <> Text.pack (show i))
    branchShape (PatCon con _) names = PatCon con (map PatVar names)
    branchShape pattern _ = pattern

    bindAt scrutinee (PatVar v) body = substitute v (Variable scrutinee) body
    bindAt _ _ body = body

isVariablePattern :: Pattern -> Bool
isVariablePattern (PatVar _) = True
isVariablePattern PatWild = True
isVariablePattern _ = False

isFallback :: Pattern -> Bool
isFallback (PatVar _) = True
isFallback PatWild = True
isFallback _ = False

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x : xs) = x : unique (filter (/= x) xs)
