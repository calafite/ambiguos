module Substitution
  ( freeVariables
  , freshIdentifier
  , substitute
  , alphaEquivalent
  ) where

import AST (Expression (..), Identifier (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

freeVariables :: Expression -> Set Identifier
freeVariables expression = case expression of
  Variable identifier ->
    Set.singleton identifier

  Universe ->
    Set.empty

  Lambda parameter body ->
    Set.delete parameter (freeVariables body)

  Application function argument ->
    Set.union (freeVariables function) (freeVariables argument)

  Pi parameter domain codomain ->
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

    Universe -> Universe

    Application function argument ->
      Application
        (substitute targetVariable replacementExpression function)
        (substitute targetVariable replacementExpression argument)

    Annotation term annotationType ->
      Annotation
        (substitute targetVariable replacementExpression term)
        (substitute targetVariable replacementExpression annotationType)

    Lambda parameter body
      | parameter == targetVariable -> Lambda parameter body
      | Set.member parameter replacementFreeVariables ->
          let freshParameter =
                freshIdentifier
                  parameter
                  (Set.unions
                    [ replacementFreeVariables
                    , freeVariables body
                    , Set.singleton targetVariable
                    ])
              renamedBody = substitute parameter (Variable freshParameter) body
          in Lambda freshParameter (substitute targetVariable replacementExpression renamedBody)
      | otherwise ->
          Lambda parameter (substitute targetVariable replacementExpression body)

    Pi parameter domain codomain ->
      let substitutedDomain = substitute targetVariable replacementExpression domain
      in if parameter == targetVariable
           then Pi parameter substitutedDomain codomain
           else if Set.member parameter replacementFreeVariables
                  then
                    let freshParameter =
                          freshIdentifier
                            parameter
                            (Set.unions
                              [ replacementFreeVariables
                              , freeVariables codomain
                              , Set.singleton targetVariable
                              ])
                        renamedCodomain = substitute parameter (Variable freshParameter) codomain
                    in Pi freshParameter substitutedDomain (substitute targetVariable replacementExpression renamedCodomain)
                  else Pi parameter substitutedDomain (substitute targetVariable replacementExpression codomain)
  where
    replacementFreeVariables = freeVariables replacementExpression

alphaEquivalent :: Expression -> Expression -> Bool
alphaEquivalent leftExpression rightExpression =
  case (leftExpression, rightExpression) of
    (Variable id1, Variable id2) ->
      id1 == id2

    (Universe, Universe) ->
      True

    (Application f1 a1, Application f2 a2) ->
      alphaEquivalent f1 f2 && alphaEquivalent a1 a2

    (Annotation t1 ty1, Annotation t2 ty2) ->
      alphaEquivalent t1 t2 && alphaEquivalent ty1 ty2

    (Lambda param1 body1, Lambda param2 body2)
      | param1 == param2 ->
          alphaEquivalent body1 body2
      | otherwise ->
          let fresh = freshIdentifier param1 (Set.union (freeVariables body1) (freeVariables body2))
              renamedBody1 = substitute param1 (Variable fresh) body1
              renamedBody2 = substitute param2 (Variable fresh) body2
          in alphaEquivalent renamedBody1 renamedBody2

    (Pi param1 dom1 codom1, Pi param2 dom2 codom2)
      | not (alphaEquivalent dom1 dom2) ->
          False
      | param1 == param2 ->
          alphaEquivalent codom1 codom2
      | otherwise ->
          let fresh = freshIdentifier param1 (Set.union (freeVariables codom1) (freeVariables codom2))
              renamedCodom1 = substitute param1 (Variable fresh) codom1
              renamedCodom2 = substitute param2 (Variable fresh) codom2
          in alphaEquivalent renamedCodom1 renamedCodom2

    _ -> False
