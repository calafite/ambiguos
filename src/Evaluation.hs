module Evaluation (
    evaluateWeakHeadNormalForm,
    normalize,
    areDefinitionallyEqual,
) where

import AST (Expression (..), Identifier)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Substitution (alphaEquivalent, substitute)

unfoldApplication :: Expression -> (Expression, [Expression])
unfoldApplication expression = collect expression []
  where
    collect (Application function argument) arguments =
        collect function (argument : arguments)
    collect headExpression arguments =
        (headExpression, arguments)

evaluateWeakHeadNormalForm :: Map Identifier Expression -> Expression -> Expression
evaluateWeakHeadNormalForm environment expression =
    case expression of
        Variable identifier ->
            case Map.lookup identifier environment of
                Just value ->
                    evaluateWeakHeadNormalForm environment value
                Nothing ->
                    Variable identifier
        Annotation term _annotationType ->
            evaluateWeakHeadNormalForm environment term
        Application function argument ->
            case evaluateWeakHeadNormalForm environment function of
                Lambda parameter _ body ->
                    evaluateWeakHeadNormalForm environment (substitute parameter argument body)
                evaluatedFunction ->
                    let combined = Application evaluatedFunction argument
                        (headExpression, arguments) = unfoldApplication combined
                     in case (headExpression, arguments) of
                            -- iota-reduction for J
                            (J, _typeA : _x : _motiveP : baseCaseD : _y : proof : remainingArguments) ->
                                let proofWhnf = evaluateWeakHeadNormalForm environment proof
                                    (proofHead, _) = unfoldApplication proofWhnf
                                 in if proofHead == Reflexivity
                                        then
                                            evaluateWeakHeadNormalForm
                                                environment
                                                (foldl Application baseCaseD remainingArguments)
                                        else combined
                            -- iota-reduction for natRec: natRec P z s zero -> z; natRec P z s (succ n) -> s n (natRec P z s n)
                            (NatRec, motiveP : baseCaseZ : stepS : targetN : remainingArguments) ->
                                let nWhnf = evaluateWeakHeadNormalForm environment targetN
                                    (nHead, nArgs) = unfoldApplication nWhnf
                                 in case nHead of
                                        Zero ->
                                            evaluateWeakHeadNormalForm
                                                environment
                                                (foldl Application baseCaseZ remainingArguments)
                                        Succ ->
                                            case nArgs of
                                                [k] ->
                                                    let recCall = foldl Application NatRec [motiveP, baseCaseZ, stepS, k]
                                                        stepResult = foldl Application stepS [k, recCall]
                                                     in evaluateWeakHeadNormalForm
                                                            environment
                                                            (foldl Application stepResult remainingArguments)
                                                _ -> combined
                                        _ -> combined
                            _ -> combined
        Universe -> Universe
        Identity -> Identity
        Reflexivity -> Reflexivity
        J -> J
        VoidType -> VoidType
        Abort -> Abort
        NatType -> NatType
        Zero -> Zero
        Succ -> Succ
        NatRec -> NatRec
        Lambda parameter maybeParameterType body ->
            Lambda parameter maybeParameterType body
        Pi parameter domain codomain ->
            Pi parameter domain codomain

normalize :: Map Identifier Expression -> Expression -> Expression
normalize environment expression =
    case evaluateWeakHeadNormalForm environment expression of
        Variable identifier ->
            Variable identifier
        Universe -> Universe
        Identity -> Identity
        Reflexivity -> Reflexivity
        J -> J
        VoidType -> VoidType
        Abort -> Abort
        NatType -> NatType
        Zero -> Zero
        Succ -> Succ
        NatRec -> NatRec
        Lambda parameter maybeParameterType body ->
            let normalizedType = fmap (normalize environment) maybeParameterType
             in Lambda parameter normalizedType (normalize environment body)
        Application function argument ->
            Application (normalize environment function) (normalize environment argument)
        Pi parameter domain codomain ->
            Pi parameter (normalize environment domain) (normalize environment codomain)
        Annotation term _annotationType ->
            normalize environment term

areDefinitionallyEqual :: Map Identifier Expression -> Expression -> Expression -> Bool
areDefinitionallyEqual environment leftExpression rightExpression =
    alphaEquivalent (normalize environment leftExpression) (normalize environment rightExpression)
