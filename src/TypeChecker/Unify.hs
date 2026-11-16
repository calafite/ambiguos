{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Unify
    ( unify
    , instantiateLeadingImplicits
    , resolveInstance
    ) where

import AST
    ( Expression (..)
    , Visibility (..)
    )
import Control.Monad.State.Strict (gets)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Evaluation (areDefinitionallyEqual, evaluateWeakHeadNormalForm)
import Substitution (freeVariables, freshIdentifier, substitute)
import TypeChecker.Meta
    ( checkPatternSpine
    , freshMeta
    , isLinear
    , solvePattern
    , stripLocated
    , unfoldApp
    , zonk
    )
import TypeChecker.Types
    ( Context (..)
    , Elab
    , ElabState (..)
    , MetaInfo (..)
    , TypeError (..)
    , UnivConstraint (..)
    , extendContextType
    , throwError
    , tryElab
    )
import TypeChecker.Universe (addUnivConstraint)

unify :: Context -> Expression -> Expression -> Elab ()
unify ctx e1 e2 = do
    z1 <- zonk (stripLocated e1)
    z2 <- zonk (stripLocated e2)
    let (h1, sp1) = unfoldApp z1
        (h2, sp2) = unfoldApp z2
    case (h1, sp1, h2, sp2) of
        (MetaVar i, [], MetaVar j, [])
            | i == j -> pure ()
            | otherwise -> do
                reg <- gets metaRegistry
                case (Map.lookup i reg, Map.lookup j reg) of
                    (Just infoI, Just infoJ) ->
                        let varsI = Map.keysSet (contextTypes (metaInfoContext infoI))
                            varsJ = Map.keysSet (contextTypes (metaInfoContext infoJ))
                         in if Set.isSubsetOf varsI varsJ
                                then solvePattern ctx j [] (MetaVar i)
                                else solvePattern ctx i [] (MetaVar j)
                    _ -> solvePattern ctx i [] (MetaVar j)
        (MetaVar i, _, MetaVar j, _)
            | i == j && sp1 == sp2 -> pure ()
        (MetaVar i, _, _, _)
            | Just spineVars <- checkPatternSpine sp1
            , isLinear spineVars ->
                tryElab (solvePattern ctx i spineVars z2) (unfoldAndRetry z1 z2)
        (_, _, MetaVar j, _)
            | Just spineVars <- checkPatternSpine sp2
            , isLinear spineVars ->
                tryElab (solvePattern ctx j spineVars z1) (unfoldAndRetry z1 z2)
        (Universe l1, [], Universe l2, []) -> do
            addUnivConstraint (ULeq l1 l2)
            pure ()
        _ -> case (z1, z2) of
            (Application v1 f1 a1, Application v2 f2 a2)
                | v1 == v2 ->
                    tryElab
                        ( do
                            unify ctx f1 f2
                            unify ctx a1 a2
                        )
                        (unfoldAndRetry z1 z2)
            (Pi v1 p1 d1 c1, Pi v2 p2 d2 c2)
                | v1 == v2 ->
                    tryElab
                        ( do
                            unify ctx d1 d2
                            if p1 == p2
                                then unify (extendContextType p1 d1 ctx) c1 c2
                                else do
                                    let fresh = freshIdentifier p1 (Set.union (freeVariables c1) (freeVariables c2))
                                        extCtx = extendContextType fresh d1 ctx
                                    unify extCtx (substitute p1 (Variable fresh) c1) (substitute p2 (Variable fresh) c2)
                        )
                        (unfoldAndRetry z1 z2)
            (Identity, Identity) -> pure ()
            (Reflexivity, Reflexivity) -> pure ()
            (J, J) -> pure ()
            (VoidType, VoidType) -> pure ()
            (Abort, Abort) -> pure ()
            (Variable x, Variable y) | x == y -> pure ()
            _ -> unfoldAndRetry z1 z2
  where
    unfoldAndRetry :: Expression -> Expression -> Elab ()
    unfoldAndRetry t1 t2 = do
        let env = contextEnv ctx
            w1 = evaluateWeakHeadNormalForm env t1
            w2 = evaluateWeakHeadNormalForm env t2
            (wh1, wsp1) = unfoldApp w1
            (wh2, wsp2) = unfoldApp w2
            fallbackDefEq =
                if w1 /= t1 || w2 /= t2
                    then unify ctx w1 w2
                    else
                        if areDefinitionallyEqual env w1 w2
                            then pure ()
                            else throwError (TypeMismatch t2 t1)
        case (wh1, wsp1, wh2, wsp2) of
            (MetaVar i, _, _, _)
                | Just spineVars <- checkPatternSpine wsp1
                , isLinear spineVars ->
                    tryElab (solvePattern ctx i spineVars w2) fallbackDefEq
            (_, _, MetaVar j, _)
                | Just spineVars <- checkPatternSpine wsp2
                , isLinear spineVars ->
                    tryElab (solvePattern ctx j spineVars w1) fallbackDefEq
            (Universe l1, [], Universe l2, []) -> do
                addUnivConstraint (ULeq l1 l2)
                pure ()
            _ -> fallbackDefEq

instantiateLeadingImplicits :: Context -> Expression -> Expression -> Elab (Expression, Expression)
instantiateLeadingImplicits context expr exprType = do
    zonkedType <- zonk exprType
    let env = contextEnv context
        whnfType = evaluateWeakHeadNormalForm env zonkedType
    case whnfType of
        Pi Implicit param domain codomain -> do
            meta <- freshMeta context domain
            let newExpr = Application Implicit expr meta
                newType = substitute param meta codomain
            instantiateLeadingImplicits context newExpr newType
        Pi Instance param domain codomain -> do
            instanceExpr <- resolveInstance context domain
            let newExpr = Application Instance expr instanceExpr
                newType = substitute param instanceExpr codomain
            instantiateLeadingImplicits context newExpr newType
        _ ->
            pure (expr, zonkedType)

resolveInstance :: Context -> Expression -> Elab Expression
resolveInstance context domain = do
    let (headExpr, _) = unfoldApp domain
        className = case headExpr of
            Variable name -> Just name
            _ -> Nothing
        localCandidates =
            [ name
            | name <- contextLocals context
            , Just ty <- [Map.lookup name (contextTypes context)]
            , areDefinitionallyEqual (contextEnv context) ty domain
            ]
        registeredCandidates = case className of
            Nothing -> []
            Just name ->
                [ instanceName
                | instanceName <- Map.findWithDefault [] name (contextInstances context)
                , Just ty <- [Map.lookup instanceName (contextTypes context)]
                , areDefinitionallyEqual (contextEnv context) ty domain
                ]
        candidates = Set.toList (Set.fromList (localCandidates ++ registeredCandidates))
    case candidates of
        [name] -> pure (Variable name)
        [] -> throwError (NoInstanceFound domain)
        names -> throwError (AmbiguousInstance domain names)
