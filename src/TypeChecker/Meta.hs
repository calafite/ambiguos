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
    , generalizeInference
    ) where

import AST
    ( CaseBranch (..)
    , Expression (..)
    , GuardedRhs (..)
    , Identifier (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad.State.Strict (gets, modify)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
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
    recordMeta False mId Nothing ctx expType
    pure (MetaVar mId)

generalizeInference :: Context -> Expression -> Expression -> Elab (Expression, Expression)
generalizeInference context body expressionType = do
    registry <- gets metaRegistry
    substitutions <- gets metaSubst
    let candidates =
            List.nub
                [ mId
                | mId <- orderedMetaIds expressionType
                , Map.notMember mId substitutions
                , Just info <- [Map.lookup mId registry]
                , not (metaIsUserHole info)
                ]
        used = Set.unions [Set.fromList (Map.keys (contextTypes context)), freeVariables expressionType, freeVariables body]
        names = freshNames used candidates
        replacements = Map.fromList (zip candidates names)
        generalizedType = replaceMetas replacements expressionType
        generalizedBody = replaceMetas replacements body
        wrap (ty, term) name =
            ( Pi Implicit name (Universe (UFixed (-1))) ty
            , Lambda Implicit name (Just (Universe (UFixed (-1)))) term
            )
        (finalType, finalBody) = foldr (\name acc -> wrap acc name) (generalizedType, generalizedBody) names
    pure (finalBody, finalType)
  where
    orderedMetaIds expression = case expression of
        MetaVar mId -> [mId]
        Application _ f a -> orderedMetaIds f ++ orderedMetaIds a
        Lambda _ _ maybeType term -> maybe [] orderedMetaIds maybeType ++ orderedMetaIds term
        Pi _ _ domain codomain -> orderedMetaIds domain ++ orderedMetaIds codomain
        Let _ maybeType definition term -> maybe [] orderedMetaIds maybeType ++ orderedMetaIds definition ++ orderedMetaIds term
        Case target motive branches ->
            orderedMetaIds target
                ++ maybe [] (orderedMetaIds . snd) motive
                ++ concatMap (concatMap (orderedMetaIds . guardedRhsBody . id) . branchRhss) branches
        Annotation term ty -> orderedMetaIds term ++ orderedMetaIds ty
        Located _ inner -> orderedMetaIds inner
        Projection term _ -> orderedMetaIds term
        RecordLiteral _ fields -> concatMap (orderedMetaIds . snd) fields
        Tuple elements -> concatMap orderedMetaIds elements
        _ -> []

    freshNames used ids =
        take (length ids) [candidate | index <- [0 ..], let candidate = nameAt index, Set.notMember candidate used]
      where
        nameAt index
            | index < 26 = Identifier (Text.singleton (toEnum (fromEnum 'a' + index)))
            | otherwise = Identifier ("a" <> Text.pack (show index))

    replaceMetas replacements expression = case expression of
        MetaVar mId -> maybe expression Variable (Map.lookup mId replacements)
        Application visibility f a -> Application visibility (replaceMetas replacements f) (replaceMetas replacements a)
        Lambda visibility parameter maybeType body -> Lambda visibility parameter (replaceMetas replacements <$> maybeType) (replaceMetas replacements body)
        Pi visibility parameter domain codomain -> Pi visibility parameter (replaceMetas replacements domain) (replaceMetas replacements codomain)
        Let parameter maybeType definition body -> Let parameter (replaceMetas replacements <$> maybeType) (replaceMetas replacements definition) (replaceMetas replacements body)
        Case target motive branches -> Case (replaceMetas replacements target) ((\(name, ty) -> (name, replaceMetas replacements ty)) <$> motive) (map replaceBranch branches)
          where
            replaceBranch branch = branch{branchRhss = map replaceRhs (branchRhss branch)}
            replaceRhs rhs = rhs{guardedRhsBody = replaceMetas replacements (guardedRhsBody rhs)}
        Annotation term ty -> Annotation (replaceMetas replacements term) (replaceMetas replacements ty)
        Located spanInfo inner -> Located spanInfo (replaceMetas replacements inner)
        Projection term field -> Projection (replaceMetas replacements term) field
        RecordLiteral recName fields -> RecordLiteral recName [(name, replaceMetas replacements value) | (name, value) <- fields]
        Tuple elements -> Tuple (map (replaceMetas replacements) elements)
        other -> other

recordMeta :: Bool -> Int -> Maybe Identifier -> Context -> Expression -> Elab ()
recordMeta isUserHole mId mName context expType = do
    let info = MetaInfo mName isUserHole expType context
    modify (\s -> s{metaRegistry = Map.insert mId info (metaRegistry s)})

collectUnsolvedGoals :: Elab [Goal]
collectUnsolvedGoals = do
    registry <- gets metaRegistry
    substMap <- gets metaSubst
    let unsolved = Map.filterWithKey (\mId info -> metaIsUserHole info && Map.notMember mId substMap) registry
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
            zonkBranch (CaseBranch pat rhss wheres) =
                CaseBranch pat <$> traverse zonkRhs rhss <*> pure wheres
              where
                zonkRhs (GuardedRhs guards body) = GuardedRhs guards <$> zonk body
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
        occursIn i target || any (\(CaseBranch _ rhss _) -> any (occursInRhs . guardedRhsBody) rhss) branches || case mMotive of
            Just (_, mt) -> occursIn i mt
            Nothing -> False
      where
        occursInRhs expr = occursIn i expr
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
