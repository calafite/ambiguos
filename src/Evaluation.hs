module Evaluation (
    evaluateWeakHeadNormalForm,
    normalize,
    areDefinitionallyEqual,
) where

import AST (Expression (..), Identifier, Visibility (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Substitution (alphaEquivalent, substitute)

unfoldApplication :: Expression -> (Expression, [(Visibility, Expression)])
unfoldApplication expression = collect expression []
  where
    collect (Application vis function argument) arguments =
        collect function ((vis, argument) : arguments)
    collect headExpression arguments =
        (headExpression, arguments)

evaluateWeakHeadNormalForm :: Map Identifier Expression -> Expression -> Expression
evaluateWeakHeadNormalForm environment expression =
    case expression of
        Variable identifier ->
            case Map.lookup identifier environment of
                Just value -> evaluateWeakHeadNormalForm environment value
                Nothing    -> Variable identifier

        Annotation term _annotationType ->
            evaluateWeakHeadNormalForm environment term

        Application vis function argument ->
            case evaluateWeakHeadNormalForm environment function of
                Lambda _ parameter _ body ->
                    evaluateWeakHeadNormalForm environment (substitute parameter argument body)
                evaluatedFunction ->
                    let combined = Application vis evaluatedFunction argument
                        (headExpression, arguments) = unfoldApplication combined
                        rawArgs = map snd arguments
                     in case (headExpression, rawArgs) of
                            (J, _typeA : _x : _motiveP : baseCaseD : _y : proof : remainingArguments) ->
                                let proofWhnf = evaluateWeakHeadNormalForm environment proof
                                    (proofHead, _) = unfoldApplication proofWhnf
                                 in if proofHead == Reflexivity
                                        then
                                            evaluateWeakHeadNormalForm
                                                environment
                                                (foldl (Application Explicit) baseCaseD remainingArguments)
                                        else combined

                            (NatRec, motiveP : baseCaseZ : stepS : targetN : remainingArguments) ->
                                let nWhnf = evaluateWeakHeadNormalForm environment targetN
                                    (nHead, nArgs) = unfoldApplication nWhnf
                                 in case nHead of
                                        Zero ->
                                            evaluateWeakHeadNormalForm
                                                environment
                                                (foldl (Application Explicit) baseCaseZ remainingArguments)
                                        Succ ->
                                            case map snd nArgs of
                                                [k] ->
                                                    let recCall = foldl (Application Explicit) NatRec [motiveP, baseCaseZ, stepS, k]
                                                        stepResult = foldl (Application Explicit) stepS [k, recCall]
                                                     in evaluateWeakHeadNormalForm
                                                            environment
                                                            (foldl (Application Explicit) stepResult remainingArguments)
                                                _ -> combined
                                        _ -> combined

                            _ -> combined

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

        Lambda vis parameter maybeParameterType body ->
            Lambda vis parameter maybeParameterType body

        Pi vis parameter domain codomain ->
            Pi vis parameter domain codomain

normalize :: Map Identifier Expression -> Expression -> Expression
normalize environment expression =
  case evaluateWeakHeadNormalForm environment expression of
    Variable identifier -> Variable identifier
    Universe            -> Universe
    Identity            -> Identity
    Reflexivity         -> Reflexivity
    J                   -> J
    VoidType            -> VoidType
    Abort               -> Abort
    NatType             -> NatType
    Zero                -> Zero
    Succ                -> Succ
    NatRec              -> NatRec
    Hole h              -> Hole h
    MetaVar i           -> MetaVar i

    Lambda vis parameter maybeParameterType body ->
      let normalizedType = fmap (normalize environment) maybeParameterType
       in Lambda vis parameter normalizedType (normalize environment body)

    Application vis function argument ->
      Application vis (normalize environment function) (normalize environment argument)

    Pi vis parameter domain codomain ->
      Pi vis parameter (normalize environment domain) (normalize environment codomain)

    Annotation term _annotationType ->
      normalize environment term

areDefinitionallyEqual :: Map Identifier Expression -> Expression -> Expression -> Bool
areDefinitionallyEqual environment leftExpression rightExpression =
  alphaEquivalent (normalize environment leftExpression) (normalize environment rightExpression)
