{-# LANGUAGE OverloadedStrings #-}

module Evaluation (
    Value (..),
    Neutral (..),
    Closure (..),
    Environment,
    emptyEnvironment,
    initEnvironment,
    evaluate,
    evaluateWeakHeadNormalForm,
    normalize,
    quote,
    areDefinitionallyEqual,
) where

import AST (CaseBranch (..), Expression (..), Identifier (..), Visibility (..))
import qualified Data.Map.Lazy as MapLazy
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Substitution (freeVariables, freshIdentifier)

-- | Lexical environment mapping identifiers to their evaluated values.
type Environment = Map Identifier Value

-- | A closure pairs an un-evaluated expression body with its lexical environment.
data Closure = Closure
    { closureParam :: !Identifier
    , closureBody :: !Expression
    , closureEnv :: !Environment
    }
    deriving (Eq, Show)

-- | Semantic values in the domain of interpretation.
data Value
    = VUniverse !Int
    | VPi !Visibility !Identifier !Value !Closure
    | VLambda !Visibility !Identifier !(Maybe Value) !Closure
    | VCon !Identifier ![(Visibility, Value)]
    | VId !Value !Value !Value
    | VRefl !Value !Value
    | VNatType
    | VZero
    | VSucc !Value
    | VVoidType
    | VHole !(Maybe Identifier)
    | VMetaVar !Int
    | VPrimIdentity ![Value]
    | VPrimReflexivity ![Value]
    | VPrimJ ![Value]
    | VPrimAbort ![Value]
    | VPrimSucc
    | VPrimNatRec ![Value]
    | VNeutral !Neutral
    deriving (Eq, Show)

-- | Neutral terms: computations blocked on an unknown variable or unsolved hole.
data Neutral
    = NVar !Identifier
    | NMetaVar !Int
    | NHole !(Maybe Identifier)
    | NApp !Neutral !Visibility !Value
    | NCase !Neutral ![CaseBranch] !Environment
    | NJ !Value !Value !Value !Value !Value !Neutral
    | NNatRec !Value !Value !Value !Neutral
    | NAbort !Value !Neutral
    | NStuck !Value
    deriving (Eq, Show)

emptyEnvironment :: Environment
emptyEnvironment = Map.empty

{- | Lazily initialize the top-level environment to permit mutually recursive or
forward-referenced definitions without evaluation order deadlocks.
Constructors bound to themselves are immediately initialized to canonical forms
to prevent blackhole recursion.
-}
initEnvironment :: Map Identifier Expression -> Environment
initEnvironment defs = env
  where
    env = MapLazy.mapWithKey evalDef defs
    evalDef ident (Variable v)
        | v == ident =
            if ident == Identifier "zero"
                then VZero
                else
                    if ident == Identifier "successor" || ident == Identifier "succ"
                        then VPrimSucc
                        else VCon ident []
    evalDef _ expr = evaluate env expr

lookupVar :: Identifier -> Environment -> Value
lookupVar ident env =
    case Map.lookup ident env of
        Just val -> val
        Nothing
            | ident == Identifier "zero" -> VZero
            | ident == Identifier "successor" || ident == Identifier "succ" -> VPrimSucc
            | otherwise -> VNeutral (NVar ident)

instantiateClosure :: Closure -> Value -> Value
instantiateClosure (Closure param body env) arg =
    evaluate (Map.insert param arg env) body

-- | Evaluation into the semantic value domain.
evaluate :: Environment -> Expression -> Value
evaluate env expression = case expression of
    Variable ident ->
        lookupVar ident env
    Universe n ->
        VUniverse n
    Annotation term _ ->
        evaluate env term
    Let param _ defExpr body ->
        let defVal = evaluate env defExpr
         in evaluate (Map.insert param defVal env) body
    Lambda vis param mType body ->
        VLambda vis param (fmap (evaluate env) mType) (Closure param body env)
    Pi vis param dom codom ->
        VPi vis param (evaluate env dom) (Closure param codom env)
    Application vis fn arg ->
        vApp vis (evaluate env fn) (evaluate env arg)
    Case target branches ->
        evalCase env (evaluate env target) branches
    Identity ->
        VPrimIdentity []
    Reflexivity ->
        VPrimReflexivity []
    J ->
        VPrimJ []
    VoidType ->
        VVoidType
    Abort ->
        VPrimAbort []
    NatType ->
        VNatType
    Zero ->
        VZero
    Succ ->
        VPrimSucc
    NatRec ->
        VPrimNatRec []
    Hole h ->
        VNeutral (NHole h)
    MetaVar i ->
        VNeutral (NMetaVar i)

evalCase :: Environment -> Value -> [CaseBranch] -> Value
evalCase env targetVal branches = case targetVal of
    VCon con args ->
        let explicitArgs = [v | (Explicit, v) <- args]
         in case matchBranch con explicitArgs branches of
                Just v -> v
                Nothing -> VNeutral (NCase (NStuck targetVal) branches env)
    VZero ->
        case matchBranch (Identifier "zero") [] branches of
            Just v -> v
            Nothing -> VNeutral (NCase (NStuck targetVal) branches env)
    VSucc k ->
        case matchBranch (Identifier "successor") [k] branches of
            Just v -> v
            Nothing ->
                case matchBranch (Identifier "succ") [k] branches of
                    Just v -> v
                    Nothing -> VNeutral (NCase (NStuck targetVal) branches env)
    VNeutral neu ->
        VNeutral (NCase neu branches env)
    other ->
        VNeutral (NCase (NStuck other) branches env)
  where
    matchBranch con args [] = Nothing
    matchBranch con args (b : bs)
        | branchConstructor b == con =
            let newEnv = foldr (\(var, val) e -> Map.insert var val e) env (zip (branchBindings b) args)
             in Just (evaluate newEnv (branchBody b))
        | otherwise = matchBranch con args bs

-- | Semantic function application.
vApp :: Visibility -> Value -> Value -> Value
vApp vis fn arg = case fn of
    VLambda _ _ _ clos ->
        instantiateClosure clos arg
    VCon con args ->
        VCon con (args ++ [(vis, arg)])
    VPrimSucc ->
        VSucc arg
    VPrimNatRec args ->
        let newArgs = args ++ [arg]
         in case newArgs of
                [p, z, s, n] -> evalNatRec p z s n
                _ -> VPrimNatRec newArgs
    VPrimJ args ->
        let newArgs = args ++ [arg]
         in case newArgs of
                [a, x, p, d, y, prf] -> evalJ a x p d y prf
                _ -> VPrimJ newArgs
    VPrimIdentity args ->
        let newArgs = args ++ [arg]
         in case newArgs of
                [a, x, y] -> VId a x y
                _ -> VPrimIdentity newArgs
    VPrimReflexivity args ->
        let newArgs = args ++ [arg]
         in case newArgs of
                [a, x] -> VRefl a x
                _ -> VPrimReflexivity newArgs
    VPrimAbort args ->
        let newArgs = args ++ [arg]
         in case newArgs of
                [a, v] -> evalAbort a v
                _ -> VPrimAbort newArgs
    VNeutral neu ->
        VNeutral (NApp neu vis arg)
    stuckVal ->
        VNeutral (NApp (NStuck stuckVal) vis arg)

-- | Primitive eliminator for Nat.
evalNatRec :: Value -> Value -> Value -> Value -> Value
evalNatRec p z s target = case target of
    VZero ->
        z
    VSucc k ->
        let recVal = evalNatRec p z s k
         in vApp Explicit (vApp Explicit s k) recVal
    VNeutral neu ->
        VNeutral (NNatRec p z s neu)
    other ->
        VNeutral (NNatRec p z s (NStuck other))

-- | Primitive eliminator for Identity (Martin-Löf J).
evalJ :: Value -> Value -> Value -> Value -> Value -> Value -> Value
evalJ typeA x motiveP baseCaseD y proof = case proof of
    VRefl _ _ ->
        baseCaseD
    VNeutral neu ->
        VNeutral (NJ typeA x motiveP baseCaseD y neu)
    other ->
        VNeutral (NJ typeA x motiveP baseCaseD y (NStuck other))

-- | Primitive eliminator for Void (ex falso quodlibet).
evalAbort :: Value -> Value -> Value
evalAbort typeA v = case v of
    VNeutral neu -> VNeutral (NAbort typeA neu)
    other -> VNeutral (NAbort typeA (NStuck other))

-- | Readback / Quoting: transforms semantic values back into normal-form expressions.
quote :: Set Identifier -> Value -> Expression
quote usedVars val = case val of
    VUniverse n ->
        Universe n
    VNatType ->
        NatType
    VZero ->
        Zero
    VSucc v ->
        Application Explicit Succ (quote usedVars v)
    VCon con args ->
        foldl (\acc (vis, a) -> Application vis acc (quote usedVars a)) (Variable con) args
    VVoidType ->
        VoidType
    VId a x y ->
        foldl
            (Application Explicit)
            Identity
            [ quote usedVars a
            , quote usedVars x
            , quote usedVars y
            ]
    VRefl a x ->
        foldl
            (Application Explicit)
            Reflexivity
            [ quote usedVars a
            , quote usedVars x
            ]
    VPrimSucc ->
        Succ
    VPrimIdentity args ->
        foldl (Application Explicit) Identity (map (quote usedVars) args)
    VPrimReflexivity args ->
        foldl (Application Explicit) Reflexivity (map (quote usedVars) args)
    VPrimJ args ->
        foldl (Application Explicit) J (map (quote usedVars) args)
    VPrimNatRec args ->
        foldl (Application Explicit) NatRec (map (quote usedVars) args)
    VPrimAbort args ->
        foldl (Application Explicit) Abort (map (quote usedVars) args)
    VHole h ->
        Hole h
    VMetaVar i ->
        MetaVar i
    VNeutral neu ->
        quoteNeutral usedVars neu
    VLambda vis param mType clos ->
        let freshParam = freshIdentifier param usedVars
            argVal = VNeutral (NVar freshParam)
            bodyVal = instantiateClosure clos argVal
            newUsed = Set.insert freshParam usedVars
            mTypeExpr = fmap (quote usedVars) mType
            bodyExpr = quote newUsed bodyVal
         in Lambda vis freshParam mTypeExpr bodyExpr
    VPi vis param dom clos ->
        let domExpr = quote usedVars dom
            freshParam = freshIdentifier param usedVars
            argVal = VNeutral (NVar freshParam)
            codomVal = instantiateClosure clos argVal
            newUsed = Set.insert freshParam usedVars
            codomExpr = quote newUsed codomVal
         in if param == Identifier "_" || Set.notMember freshParam (freeVariables codomExpr)
                then Pi vis (Identifier "_") domExpr codomExpr
                else Pi vis freshParam domExpr codomExpr

quoteNeutral :: Set Identifier -> Neutral -> Expression
quoteNeutral usedVars neu = case neu of
    NVar ident ->
        Variable ident
    NMetaVar i ->
        MetaVar i
    NHole h ->
        Hole h
    NApp fn vis arg ->
        Application vis (quoteNeutral usedVars fn) (quote usedVars arg)
    NCase target branches env ->
        let quoteBranch (CaseBranch con vars body) =
                let (freshes, newEnv, newUsed) =
                        foldr
                            ( \v (fs, e, u) ->
                                let f = freshIdentifier v u
                                 in (f : fs, Map.insert v (VNeutral (NVar f)) e, Set.insert f u)
                            )
                            ([], env, usedVars)
                            vars
                    bVal = evaluate newEnv body
                 in CaseBranch con freshes (quote newUsed bVal)
         in Case (quoteNeutral usedVars target) (map quoteBranch branches)
    NJ a x p d y prf ->
        foldl
            (Application Explicit)
            J
            [ quote usedVars a
            , quote usedVars x
            , quote usedVars p
            , quote usedVars d
            , quote usedVars y
            , quoteNeutral usedVars prf
            ]
    NNatRec p z s nNeu ->
        foldl
            (Application Explicit)
            NatRec
            [ quote usedVars p
            , quote usedVars z
            , quote usedVars s
            , quoteNeutral usedVars nNeu
            ]
    NAbort a vNeu ->
        foldl
            (Application Explicit)
            Abort
            [ quote usedVars a
            , quoteNeutral usedVars vNeu
            ]
    NStuck v ->
        quote usedVars v

-- | Evaluates an expression to weak head normal form.
evaluateWeakHeadNormalForm :: Map Identifier Expression -> Expression -> Expression
evaluateWeakHeadNormalForm defs expr =
    let env = initEnvironment defs
        val = evaluate env expr
        usedVars = Map.keysSet defs `Set.union` freeVariables expr
     in quote usedVars val

-- | Fully normalizes an expression (evaluates under binders).
normalize :: Map Identifier Expression -> Expression -> Expression
normalize defs expr =
    let env = initEnvironment defs
        val = evaluate env expr
        usedVars = Map.keysSet defs `Set.union` freeVariables expr
     in quote usedVars val

-- | Definitional equality check with semantic eta-conversion.
areDefinitionallyEqual :: Map Identifier Expression -> Expression -> Expression -> Bool
areDefinitionallyEqual defs e1 e2 =
    let env = initEnvironment defs
        v1 = evaluate env e1
        v2 = evaluate env e2
        usedVars =
            Map.keysSet defs
                `Set.union` freeVariables e1
                `Set.union` freeVariables e2
     in equalVal usedVars v1 v2

equalVal :: Set Identifier -> Value -> Value -> Bool
equalVal usedVars v1 v2 = case (v1, v2) of
    (VUniverse i, VUniverse j) ->
        i == -1 || j == -1 || i == j
    (VNatType, VNatType) ->
        True
    (VZero, VZero) ->
        True
    (VSucc k1, VSucc k2) ->
        equalVal usedVars k1 k2
    (VCon c1 args1, VCon c2 args2) ->
        c1 == c2
            && length args1 == length args2
            && and [vis1 == vis2 && equalVal usedVars a1 a2 | ((vis1, a1), (vis2, a2)) <- zip args1 args2]
    (VVoidType, VVoidType) ->
        True
    (VId a1 x1 y1, VId a2 x2 y2) ->
        equalVal usedVars a1 a2 && equalVal usedVars x1 x2 && equalVal usedVars y1 y2
    (VRefl a1 x1, VRefl a2 x2) ->
        equalVal usedVars a1 a2 && equalVal usedVars x1 x2
    (VPrimSucc, VPrimSucc) ->
        True
    (VPrimIdentity args1, VPrimIdentity args2) ->
        equalValList usedVars args1 args2
    (VPrimReflexivity args1, VPrimReflexivity args2) ->
        equalValList usedVars args1 args2
    (VPrimJ args1, VPrimJ args2) ->
        equalValList usedVars args1 args2
    (VPrimNatRec args1, VPrimNatRec args2) ->
        equalValList usedVars args1 args2
    (VPrimAbort args1, VPrimAbort args2) ->
        equalValList usedVars args1 args2
    (VHole h1, VHole h2) ->
        h1 == h2
    (VMetaVar i, VMetaVar j) ->
        i == j
    (VNeutral n1, VNeutral n2) ->
        equalNeutral usedVars n1 n2
    (VLambda vis1 param1 _ clos1, VLambda vis2 _ _ clos2)
        | vis1 == vis2 ->
            let freshParam = freshIdentifier param1 usedVars
                argVal = VNeutral (NVar freshParam)
                newUsed = Set.insert freshParam usedVars
             in equalVal newUsed (instantiateClosure clos1 argVal) (instantiateClosure clos2 argVal)
    -- Extensional eta-equality for functions
    (VLambda vis1 param1 _ clos1, other) ->
        let freshParam = freshIdentifier param1 usedVars
            argVal = VNeutral (NVar freshParam)
            newUsed = Set.insert freshParam usedVars
         in equalVal newUsed (instantiateClosure clos1 argVal) (vApp vis1 other argVal)
    (other, VLambda vis2 param2 _ clos2) ->
        let freshParam = freshIdentifier param2 usedVars
            argVal = VNeutral (NVar freshParam)
            newUsed = Set.insert freshParam usedVars
         in equalVal newUsed (vApp vis2 other argVal) (instantiateClosure clos2 argVal)
    (VPi vis1 param1 dom1 clos1, VPi vis2 _ dom2 clos2)
        | vis1 == vis2 ->
            equalVal usedVars dom1 dom2
                && let freshParam = freshIdentifier param1 usedVars
                       argVal = VNeutral (NVar freshParam)
                       newUsed = Set.insert freshParam usedVars
                    in equalVal newUsed (instantiateClosure clos1 argVal) (instantiateClosure clos2 argVal)
    _ -> False
  where
    equalValList u xs ys =
        length xs == length ys && and (zipWith (equalVal u) xs ys)

equalNeutral :: Set Identifier -> Neutral -> Neutral -> Bool
equalNeutral usedVars neu1 neu2 = case (neu1, neu2) of
    (NVar x1, NVar x2) ->
        x1 == x2
    (NMetaVar i, NMetaVar j) ->
        i == j
    (NHole h1, NHole h2) ->
        h1 == h2
    (NApp f1 v1 a1, NApp f2 v2 a2) ->
        v1 == v2 && equalNeutral usedVars f1 f2 && equalVal usedVars a1 a2
    (NJ a1 x1 p1 d1 y1 prf1, NJ a2 x2 p2 d2 y2 prf2) ->
        equalVal usedVars a1 a2
            && equalVal usedVars x1 x2
            && equalVal usedVars p1 p2
            && equalVal usedVars d1 d2
            && equalVal usedVars y1 y2
            && equalNeutral usedVars prf1 prf2
    (NCase n1 bs1 _, NCase n2 bs2 _) ->
        equalNeutral usedVars n1 n2 && length bs1 == length bs2
    (NNatRec p1 z1 s1 n1, NNatRec p2 z2 s2 n2) ->
        equalVal usedVars p1 p2
            && equalVal usedVars z1 z2
            && equalVal usedVars s1 s2
            && equalNeutral usedVars n1 n2
    (NAbort a1 v1, NAbort a2 v2) ->
        equalVal usedVars a1 a2 && equalNeutral usedVars v1 v2
    (NStuck s1, NStuck s2) ->
        equalVal usedVars s1 s2
    _ -> False
