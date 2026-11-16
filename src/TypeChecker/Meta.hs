{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Meta
    ( freshMetaId
    , freshMeta
    , recordMeta
    , collectUnsolvedGoals
    , zonk
    , occursIn
    , unfoldApp
    , stripLocated
    , checkPatternSpine
    , isLinear
    , solvePattern
    ) where

import AST
    ( CaseBranch (..)
    , Expression (..)
    , Identifier (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad.State.Strict (gets, modify)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Evaluation (evaluateWeakHeadNormalForm)
import Substitution (freeVariables)
import TypeChecker.Types
    ( Context (..)
    , Elab
    , ElabState (..)
    , Goal (..)
    , MetaInfo (..)
    , TypeError (..)
    , throwError
    )

freshMetaId :: Elab Int
freshMetaId = do
    idx <- gets nextMetaId
    modify (\s -> s{nextMetaId = idx + 1})
    pure idx

freshMeta :: Context -> Expression -> Elab Expression
freshMeta ctx expType = do
    mId <- freshMetaId
    recordMeta mId Nothing ctx expType
    pure (MetaVar mId)

recordMeta :: Int -> Maybe Identifier -> Context -> Expression -> Elab ()
recordMeta mId mName context expType = do
    let info = MetaInfo mName expType context
    modify (\s -> s{metaRegistry = Map.insert mId info (metaRegistry s)})

collectUnsolvedGoals :: Elab [Goal]
collectUnsolvedGoals = do
    registry <- gets metaRegistry
    substMap <- gets metaSubst
    let unsolved = Map.filterWithKey (\mId _ -> Map.notMember mId substMap) registry
    traverse toGoal (Map.toList unsolved)
  where
    toGoal (mId, info) = do
        zonkedExp <- zonk (metaInfoExpected info)
        let ctx = metaInfoContext info
            env = contextEnv ctx
            normExp = evaluateWeakHeadNormalForm env zonkedExp
        locals <- traverse (zonkLocal ctx) (contextLocals ctx)
        pure
            Goal
                { goalId = mId
                , goalName = metaInfoName info
                , goalExpected = normExp
                , goalLocals = locals
                }

    zonkLocal ctx ident = do
        let rawType = Map.findWithDefault (Universe (UFixed (-1))) ident (contextTypes ctx)
        zonkedType <- zonk rawType
        let normType = evaluateWeakHeadNormalForm (contextEnv ctx) zonkedType
        pure (ident, normType)

zonk :: Expression -> Elab Expression
zonk expr = do
    substMap <- gets metaSubst
    case expr of
        MetaVar i ->
            case Map.lookup i substMap of
                Just resolved -> zonk resolved
                Nothing -> pure (MetaVar i)
        Application vis f a -> Application vis <$> zonk f <*> zonk a
        Lambda vis p ty body -> Lambda vis p <$> traverse zonk ty <*> zonk body
        Pi vis p d c -> Pi vis p <$> zonk d <*> zonk c
        Let p ty d b -> Let p <$> traverse zonk ty <*> zonk d <*> zonk b
        Case target mMotive branches ->
            Case <$> zonk target <*> traverse zonkMotive mMotive <*> traverse zonkBranch branches
          where
            zonkMotive (mv, mt) = (,) mv <$> zonk mt
            zonkBranch (CaseBranch pat body) = CaseBranch pat <$> zonk body
        Annotation t ty -> Annotation <$> zonk t <*> zonk ty
        Located sp e -> Located sp <$> zonk e
        other -> pure other

occursIn :: Int -> Expression -> Bool
occursIn i expr = case expr of
    MetaVar j -> i == j
    Application _ f a -> occursIn i f || occursIn i a
    Lambda _ _ ty body -> maybe False (occursIn i) ty || occursIn i body
    Pi _ _ d c -> occursIn i d || occursIn i c
    Let _ ty d b -> maybe False (occursIn i) ty || occursIn i d || occursIn i b
    Case target mMotive branches ->
        occursIn i target || any (\(CaseBranch _ b) -> occursIn i b) branches || case mMotive of
            Just (_, mt) -> occursIn i mt
            Nothing -> False
    Annotation t ty -> occursIn i t || occursIn i ty
    Located _ e -> occursIn i e
    _ -> False

unfoldApp :: Expression -> (Expression, [(Visibility, Expression)])
unfoldApp expression = collect expression []
  where
    collect (Application vis fn arg) args = collect (stripLocated fn) ((vis, arg) : args)
    collect headExpr args = (stripLocated headExpr, args)

stripLocated :: Expression -> Expression
stripLocated (Located _ e) = stripLocated e
stripLocated e = e

checkPatternSpine :: [(Visibility, Expression)] -> Maybe [(Visibility, Identifier)]
checkPatternSpine = traverse extractVar
  where
    extractVar (vis, Variable ident) = Just (vis, ident)
    extractVar _ = Nothing

isLinear :: [(Visibility, Identifier)] -> Bool
isLinear vars =
    let idents = map snd vars
     in Set.size (Set.fromList idents) == length idents

solvePattern :: Context -> Int -> [(Visibility, Identifier)] -> Expression -> Elab ()
solvePattern ctx mId spine rhs = do
    zonkedRhs <- zonk rhs
    if occursIn mId zonkedRhs
        then throwError (OccursCheckFailed mId zonkedRhs)
        else do
            reg <- gets metaRegistry
            let allowedVars = case Map.lookup mId reg of
                    Just info -> Map.keysSet (contextTypes (metaInfoContext info))
                    Nothing -> Map.keysSet (contextTypes ctx)
                spineVarSet = Set.fromList (map snd spine)
                validVars = Set.union allowedVars spineVarSet
                rhsFreeVars = freeVariables zonkedRhs
                escapingVars = Set.difference rhsFreeVars validVars
            case Set.lookupMin escapingVars of
                Just escaped ->
                    throwError (ScopeEscapeFailed mId escaped zonkedRhs)
                Nothing -> do
                    let solution = foldr (\(vis, param) body -> Lambda vis param Nothing body) zonkedRhs spine
                    modify (\s -> s{metaSubst = Map.insert mId solution (metaSubst s)})
