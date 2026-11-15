{-# LANGUAGE OverloadedStrings #-}

module Substitution (
    freeVariables,
    freshIdentifier,
    substitute,
    alphaEquivalent,
) where

import AST (CaseBranch (..), Expression (..), Identifier (..), Pattern (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

freeVariables :: Expression -> Set Identifier
freeVariables expression = case expression of
    Variable identifier -> Set.singleton identifier
    Universe _ -> Set.empty
    Identity -> Set.empty
    Reflexivity -> Set.empty
    J -> Set.empty
    VoidType -> Set.empty
    Abort -> Set.empty
    NatType -> Set.empty
    Zero -> Set.empty
    Succ -> Set.empty
    NatRec -> Set.empty
    Hole _ -> Set.empty
    MetaVar _ -> Set.empty
    Located _ e -> freeVariables e
    Projection term _ -> freeVariables term
    RecordLiteral _ fields -> Set.unions (map (freeVariables . snd) fields)
    Tuple elements -> Set.unions (map freeVariables elements)
    PatternCase target motive branches ->
        Set.unions (freeVariables target : maybe [] (\(_, t) -> [freeVariables t]) motive ++ [freeVariables body | (_, body) <- branches])
    Literal _ -> Set.empty
    PrimType _ -> Set.empty
    PrimOp _ -> Set.empty
    Case target (Just (mv, mtype)) branches ->
        let targetVars = freeVariables target
            motiveVars = Set.delete mv (freeVariables mtype)
            branchVars (CaseBranch pat body) = foldr Set.delete (freeVariables body) (patternBindings pat)
         in Set.unions (targetVars : motiveVars : map branchVars branches)
    Case target Nothing branches ->
        let targetVars = freeVariables target
            branchVars (CaseBranch pat body) = foldr Set.delete (freeVariables body) (patternBindings pat)
         in Set.unions (targetVars : map branchVars branches)
    Let param maybeParamType defExpr body ->
        let typeFreeVars = maybe Set.empty freeVariables maybeParamType
            defFreeVars = freeVariables defExpr
            bodyFreeVars = Set.delete param (freeVariables body)
         in Set.unions [typeFreeVars, defFreeVars, bodyFreeVars]
    Lambda _ parameter maybeParameterType body ->
        let typeFreeVariables = case maybeParameterType of
                Just parameterType -> freeVariables parameterType
                Nothing -> Set.empty
            bodyFreeVariables = Set.delete parameter (freeVariables body)
         in Set.union typeFreeVariables bodyFreeVariables
    Application _ function argument ->
        Set.union (freeVariables function) (freeVariables argument)
    Pi _ parameter domain codomain ->
        Set.union (freeVariables domain) (Set.delete parameter (freeVariables codomain))
    Annotation term annotationType ->
        Set.union (freeVariables term) (freeVariables annotationType)

freshIdentifier :: Identifier -> Set Identifier -> Identifier
freshIdentifier (Identifier baseName) usedIdentifiers =
    findUnused candidateIdentifiers
  where
    candidateIdentifiers =
        Identifier baseName
            : [ Identifier (baseName <> Text.pack (show index))
              | index <- [(1 :: Integer) ..]
              ]

    findUnused (candidate : remaining)
        | Set.notMember candidate usedIdentifiers = candidate
        | otherwise = findUnused remaining
    findUnused [] = Identifier (baseName <> "_fresh")

patternBindings :: Pattern -> [Identifier]
patternBindings (PatVar v) = [v]
patternBindings PatWild = []
patternBindings (PatLit _) = []
patternBindings (PatCon _ ps) = concatMap patternBindings ps
patternBindings (PatTuple ps) = concatMap patternBindings ps

alphaPattern :: Pattern -> Pattern -> Expression -> Expression -> Bool
alphaPattern p1 p2 b1 b2 =
    shape p1 p2
        && length vs1 == length vs2
        && let used = Set.unions [freeVariables b1, freeVariables b2]
               fresh = map (\v -> freshIdentifier v used) vs1
               renameAll body = foldr (\(v, f) b -> substitute v (Variable f) b) body (zip vs1 fresh)
           in alphaEquivalent (renameAll b1) (renameAll (foldr (\(v, f) b -> substitute v (Variable f) b) b2 (zip vs2 fresh)))
  where
    vs1 = patternBindings p1
    vs2 = patternBindings p2
    shape (PatVar _) (PatVar _) = True
    shape PatWild PatWild = True
    shape (PatLit x) (PatLit y) = x == y
    shape (PatCon c xs) (PatCon d ys) = c == d && length xs == length ys && and (zipWith (\a b -> shapeOnly a b) xs ys)
    shape (PatTuple xs) (PatTuple ys) = length xs == length ys && and (zipWith shapeOnly xs ys)
    shape _ _ = False
    shapeOnly (PatVar _) (PatVar _) = True
    shapeOnly PatWild PatWild = True
    shapeOnly (PatLit x) (PatLit y) = x == y
    shapeOnly (PatCon c xs) (PatCon d ys) = c == d && length xs == length ys && and (zipWith shapeOnly xs ys)
    shapeOnly (PatTuple xs) (PatTuple ys) = length xs == length ys && and (zipWith shapeOnly xs ys)
    shapeOnly _ _ = False

substitute :: Identifier -> Expression -> Expression -> Expression
substitute targetVariable replacementExpression sourceExpression =
    case sourceExpression of
        Variable identifier
            | identifier == targetVariable -> replacementExpression
            | otherwise -> Variable identifier
        Universe n -> Universe n
        Identity -> Identity
        Reflexivity -> Reflexivity
        J -> J
        VoidType -> VoidType
        Abort -> Abort
        NatType -> NatType
        Zero -> Zero
        Succ -> Succ
        NatRec -> NatRec
        Projection term field -> Projection (substitute targetVariable replacementExpression term) field
        RecordLiteral name fields -> RecordLiteral name [(f, substitute targetVariable replacementExpression e) | (f, e) <- fields]
        Tuple elements -> Tuple (map (substitute targetVariable replacementExpression) elements)
        PatternCase target motive branches ->
            PatternCase (substitute targetVariable replacementExpression target)
                (fmap (\(v, t) -> (v, substitute targetVariable replacementExpression t)) motive)
                [(p, substitute targetVariable replacementExpression e) | (p, e) <- branches]
        Literal literal -> Literal literal
        PrimType primitiveType -> PrimType primitiveType
        PrimOp operation -> PrimOp operation
        Hole h -> Hole h
        MetaVar i -> MetaVar i
        Located sp e -> Located sp (substitute targetVariable replacementExpression e)
        Case target mMotive branches ->
            Case
                (substitute targetVariable replacementExpression target)
                (fmap (\(mv, mt) -> (mv, substitute targetVariable replacementExpression mt)) mMotive)
                (map substBranch branches)
          where
            substBranch (CaseBranch pat body)
                | elem targetVariable bound = CaseBranch pat body
                | any (`Set.member` replacementFreeVariables) bound =
                    let (newPat, renamedBody) = renamePattern pat body (Set.unions [replacementFreeVariables, freeVariables body, Set.singleton targetVariable])
                     in CaseBranch newPat (substitute targetVariable replacementExpression renamedBody)
                | otherwise =
                    CaseBranch pat (substitute targetVariable replacementExpression body)
              where bound = patternBindings pat

            renamePattern pat body used =
                foldl renameOne (pat, body) (patternBindings pat)
              where
                renameOne (p, b) v =
                    let fresh = freshIdentifier v used
                     in (renamePat v fresh p, substitute v (Variable fresh) b)
                renamePat v fresh (PatVar x) | x == v = PatVar fresh
                renamePat _ _ (PatVar x) = PatVar x
                renamePat _ _ PatWild = PatWild
                renamePat _ _ (PatLit l) = PatLit l
                renamePat v fresh (PatCon c ps) = PatCon c (map (renamePat v fresh) ps)
                renamePat v fresh (PatTuple ps) = PatTuple (map (renamePat v fresh) ps)
        Let param maybeParamType defExpr body ->
            let substType = fmap (substitute targetVariable replacementExpression) maybeParamType
                substDef = substitute targetVariable replacementExpression defExpr
                typeFreeVars = maybe Set.empty freeVariables maybeParamType
             in if param == targetVariable
                    then Let param substType substDef body
                    else
                        if Set.member param replacementFreeVariables
                            then
                                let freshParam =
                                        freshIdentifier
                                            param
                                            ( Set.unions
                                                [ replacementFreeVariables
                                                , freeVariables body
                                                , typeFreeVars
                                                , Set.singleton targetVariable
                                                ]
                                            )
                                    renamedBody = substitute param (Variable freshParam) body
                                 in Let freshParam substType substDef (substitute targetVariable replacementExpression renamedBody)
                            else Let param substType substDef (substitute targetVariable replacementExpression body)
        Application vis function argument ->
            Application
                vis
                (substitute targetVariable replacementExpression function)
                (substitute targetVariable replacementExpression argument)
        Annotation term annotationType ->
            Annotation
                (substitute targetVariable replacementExpression term)
                (substitute targetVariable replacementExpression annotationType)
        Lambda vis parameter maybeParameterType body ->
            let substitutedType = fmap (substitute targetVariable replacementExpression) maybeParameterType
                typeFreeVariables = case maybeParameterType of
                    Just parameterType -> freeVariables parameterType
                    Nothing -> Set.empty
             in if parameter == targetVariable
                    then Lambda vis parameter substitutedType body
                    else
                        if Set.member parameter replacementFreeVariables
                            then
                                let freshParameter =
                                        freshIdentifier
                                            parameter
                                            ( Set.unions
                                                [ replacementFreeVariables
                                                , freeVariables body
                                                , typeFreeVariables
                                                , Set.singleton targetVariable
                                                ]
                                            )
                                    renamedBody = substitute parameter (Variable freshParameter) body
                                 in Lambda vis freshParameter substitutedType (substitute targetVariable replacementExpression renamedBody)
                            else Lambda vis parameter substitutedType (substitute targetVariable replacementExpression body)
        Pi vis parameter domain codomain ->
            let substitutedDomain = substitute targetVariable replacementExpression domain
             in if parameter == targetVariable
                    then Pi vis parameter substitutedDomain codomain
                    else
                        if Set.member parameter replacementFreeVariables
                            then
                                let freshParameter =
                                        freshIdentifier
                                            parameter
                                            ( Set.unions
                                                [ replacementFreeVariables
                                                , freeVariables codomain
                                                , Set.singleton targetVariable
                                                ]
                                            )
                                    renamedCodomain = substitute parameter (Variable freshParameter) codomain
                                 in Pi vis freshParameter substitutedDomain (substitute targetVariable replacementExpression renamedCodomain)
                            else Pi vis parameter substitutedDomain (substitute targetVariable replacementExpression codomain)
  where
    replacementFreeVariables = freeVariables replacementExpression

alphaEquivalent :: Expression -> Expression -> Bool
alphaEquivalent leftExpression rightExpression =
    case (leftExpression, rightExpression) of
        (Variable id1, Variable id2) -> id1 == id2
        (Universe i, Universe j) -> i == j
        (Identity, Identity) -> True
        (Reflexivity, Reflexivity) -> True
        (J, J) -> True
        (VoidType, VoidType) -> True
        (Abort, Abort) -> True
        (NatType, NatType) -> True
        (Zero, Zero) -> True
        (Succ, Succ) -> True
        (NatRec, NatRec) -> True
        (Hole _, Hole _) -> True
        (MetaVar i, MetaVar j) -> i == j
        (Case t1 (Just (mv1, mtype1)) bs1, Case t2 (Just (mv2, mtype2)) bs2) ->
            let freshMotive = freshIdentifier mv1 (Set.unions [freeVariables mtype1, freeVariables mtype2])
                mtype1' = substitute mv1 (Variable freshMotive) mtype1
                mtype2' = substitute mv2 (Variable freshMotive) mtype2
             in alphaEquivalent t1 t2
                && alphaEquivalent mtype1' mtype2'
                && length bs1 == length bs2
                && and (zipWith branchEq bs1 bs2)
          where
            branchEq (CaseBranch p1 b1) (CaseBranch p2 b2) =
                alphaPattern p1 p2 b1 b2
        (Case t1 Nothing bs1, Case t2 Nothing bs2) ->
            alphaEquivalent t1 t2 && length bs1 == length bs2 && and (zipWith branchEq bs1 bs2)
          where
            branchEq (CaseBranch p1 b1) (CaseBranch p2 b2) = alphaPattern p1 p2 b1 b2
        (Case _ (Just _) _, Case _ Nothing _) -> False
        (Case _ Nothing _, Case _ (Just _) _) -> False
        (Let p1 ty1 d1 b1, Let p2 ty2 d2 b2) ->
            let typesMatch = case (ty1, ty2) of
                    (Nothing, Nothing) -> True
                    (Just t1, Just t2) -> alphaEquivalent t1 t2
                    _ -> False
             in typesMatch
                    && alphaEquivalent d1 d2
                    && if p1 == p2
                        then alphaEquivalent b1 b2
                        else
                            let fresh = freshIdentifier p1 (Set.union (freeVariables b1) (freeVariables b2))
                                renamed1 = substitute p1 (Variable fresh) b1
                                renamed2 = substitute p2 (Variable fresh) b2
                             in alphaEquivalent renamed1 renamed2
        (Application v1 f1 a1, Application v2 f2 a2) ->
            v1 == v2 && alphaEquivalent f1 f2 && alphaEquivalent a1 a2
        (Annotation t1 ty1, Annotation t2 ty2) ->
            alphaEquivalent t1 t2 && alphaEquivalent ty1 ty2
        (Tuple es1, Tuple es2) -> length es1 == length es2 && and (zipWith alphaEquivalent es1 es2)
        (Lambda v1 param1 type1 body1, Lambda v2 param2 type2 body2) ->
            let typesMatch = case (type1, type2) of
                    (Nothing, Nothing) -> True
                    (Just t1, Just t2) -> alphaEquivalent t1 t2
                    _ -> False
             in if v1 /= v2 || not typesMatch
                    then False
                    else
                        if param1 == param2
                            then alphaEquivalent body1 body2
                            else
                                let fresh = freshIdentifier param1 (Set.union (freeVariables body1) (freeVariables body2))
                                    renamedBody1 = substitute param1 (Variable fresh) body1
                                    renamedBody2 = substitute param2 (Variable fresh) body2
                                 in alphaEquivalent renamedBody1 renamedBody2
        (Pi v1 param1 dom1 codom1, Pi v2 param2 dom2 codom2)
            | v1 /= v2 || not (alphaEquivalent dom1 dom2) -> False
            | param1 == param2 -> alphaEquivalent codom1 codom2
            | otherwise ->
                let fresh = freshIdentifier param1 (Set.union (freeVariables codom1) (freeVariables codom2))
                    renamedCodom1 = substitute param1 (Variable fresh) codom1
                    renamedCodom2 = substitute param2 (Variable fresh) codom2
                 in alphaEquivalent renamedCodom1 renamedCodom2
        (Located _ e1, e2) -> alphaEquivalent e1 e2
        (e1, Located _ e2) -> alphaEquivalent e1 e2
        _ -> False
