{-# LANGUAGE OverloadedStrings #-}

module Substitution (
    freeVariables,
    freshIdentifier,
    substitute,
    alphaEquivalent,
) where

import AST (Expression (..), Identifier (..), Visibility (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

freeVariables :: Expression -> Set Identifier
freeVariables expression = case expression of
    Variable identifier -> Set.singleton identifier
    Universe            -> Set.empty
    Identity            -> Set.empty
    Reflexivity         -> Set.empty
    J                   -> Set.empty
    VoidType            -> Set.empty
    Abort               -> Set.empty
    NatType             -> Set.empty
    Zero                -> Set.empty
    Succ                -> Set.empty
    NatRec              -> Set.empty
    Hole _              -> Set.empty
    MetaVar _           -> Set.empty

    Lambda _ parameter maybeParameterType body ->
        let typeFreeVariables = case maybeParameterType of
                Just parameterType -> freeVariables parameterType
                Nothing            -> Set.empty
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

substitute :: Identifier -> Expression -> Expression -> Expression
substitute targetVariable replacementExpression sourceExpression =
    case sourceExpression of
        Variable identifier
            | identifier == targetVariable -> replacementExpression
            | otherwise -> Variable identifier

        Universe    -> Universe
        Identity    -> Identity
        Reflexivity -> Reflexivity
        J           -> J
        VoidType    -> VoidType
        Abort       -> Abort
        NatType     -> NatType
        Zero        -> Zero
        Succ        -> Succ
        NatRec      -> NatRec
        Hole h      -> Hole h
        MetaVar i   -> MetaVar i

        Application vis function argument ->
            Application vis
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
                    Nothing            -> Set.empty
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
        (Universe, Universe)         -> True
        (Identity, Identity)         -> True
        (Reflexivity, Reflexivity)   -> True
        (J, J)                       -> True
        (VoidType, VoidType)         -> True
        (Abort, Abort)               -> True
        (NatType, NatType)           -> True
        (Zero, Zero)                 -> True
        (Succ, Succ)                 -> True
        (NatRec, NatRec)             -> True
        (Hole _, Hole _)             -> True
        (MetaVar i, MetaVar j)       -> i == j

        (Application v1 f1 a1, Application v2 f2 a2) ->
            v1 == v2 && alphaEquivalent f1 f2 && alphaEquivalent a1 a2

        (Annotation t1 ty1, Annotation t2 ty2) ->
            alphaEquivalent t1 t2 && alphaEquivalent ty1 ty2

        (Lambda v1 param1 type1 body1, Lambda v2 param2 type2 body2) ->
            let typesMatch = case (type1, type2) of
                    (Nothing, Nothing) -> True
                    (Just t1, Just t2) -> alphaEquivalent t1 t2
                    _                  -> False
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
            | param1 == param2                            -> alphaEquivalent codom1 codom2
            | otherwise                                   ->
                let fresh = freshIdentifier param1 (Set.union (freeVariables codom1) (freeVariables codom2))
                    renamedCodom1 = substitute param1 (Variable fresh) codom1
                    renamedCodom2 = substitute param2 (Variable fresh) codom2
                 in alphaEquivalent renamedCodom1 renamedCodom2

        _ -> False
