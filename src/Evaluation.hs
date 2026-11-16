{-# LANGUAGE OverloadedStrings #-}

module Evaluation (
    Value (..),
    Neutral (..),
    Closure (..),
    Environment,
    emptyEnvironment,
    evaluate,
    evaluateWeakHeadNormalForm,
    normalize,
    quote,
    areDefinitionallyEqual,
) where

import AST (CaseBranch (..), Expression (..), Guard (..), GuardedRhs (..), Identifier (..), Literal (..), Pattern (..), PrimOp (..), PrimType (..), UniverseLevel (..), Visibility (..))
import Control.Monad (zipWithM)
import Data.Char (chr)
import Data.Text (Text)
import qualified Data.Text as Text
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
    , closureEnv :: Environment
    }
    deriving (Eq, Show)

-- | Semantic values in the domain of interpretation.
data Value
    = VUniverse UniverseLevel
    | VPi !Visibility !Identifier !Value !Closure
    | VLambda !Visibility !Identifier !(Maybe Value) !Closure
    | VCon !Identifier ![(Visibility, Value)]
    | VId !Value !Value !Value
    | VRefl !Value !Value
    | VVoidType
    | VPrimType !PrimType
    | VLit !Literal
    | VPrimOp !PrimOp ![Value]
    | VHole !(Maybe Identifier)
    | VMetaVar !Int
    | VPrimIdentity ![Value]
    | VPrimReflexivity ![Value]
    | VPrimJ ![Value]
    | VPrimAbort ![Value]
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
    | NAbort !Value !Neutral
    | NStuck !Value
    | NPrimOp !PrimOp ![Value]
    deriving (Eq, Show)

emptyEnvironment :: Environment
emptyEnvironment = Map.empty

lookupVar :: Identifier -> Environment -> Value
lookupVar ident env =
    case ident of
        Identifier "[]" -> VCon ident []
        Identifier ":" -> VCon ident []
        _ -> case Map.lookup ident env of
            Just val -> val
            Nothing -> VNeutral (NVar ident)

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
    Projection term field ->
        vApp Explicit (lookupVar field env) (evaluate env term)
    RecordLiteral name fields ->
        let constructor = lookupVar (Identifier ("mk" <> unIdentifier name)) env
         in foldl (vApp Explicit) constructor (map (evaluate env . snd) fields)
    Literal literal -> VLit literal
    PrimType primitiveType -> VPrimType primitiveType
    PrimOp operation -> VPrimOp operation []
    Case target _ branches ->
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
    Hole h ->
        VNeutral (NHole h)
    MetaVar i ->
        VNeutral (NMetaVar i)
    Located _ e ->
        evaluate env e

evalCase :: Environment -> Value -> [CaseBranch] -> Value
evalCase env targetVal branches =
    case matchBranches env targetVal branches of
        Just res -> res
        Nothing -> VNeutral (NCase (case targetVal of VNeutral neu -> neu; other -> NStuck other) branches env)
  where
    matchBranches _ _ [] = Nothing
    matchBranches e v (CaseBranch pat rhss _ : bs) =
        case tryMatch pat v of
            Just bindings -> Just (evaluate (foldr (uncurry Map.insert) e bindings) (guardedRhsBody (head rhss)))
            Nothing -> matchBranches e v bs
    tryMatch PatWild _ = Just []
    tryMatch (PatVar x) v = Just [(x, v)]
    tryMatch (PatLit lit) (VLit vlit) | lit == vlit = Just []
    tryMatch (PatLit _) _ = Nothing
    tryMatch (PatCon (Identifier "[]") []) (VLit (LitString s))
        | Text.null s = Just []
    tryMatch (PatCon (Identifier ":") [pHead, pTail]) (VLit (LitString s)) =
        case Text.uncons s of
            Just (c, rest) -> concat <$> zipWithM tryMatch [pHead, pTail] [VLit (LitChar c), VLit (LitString rest)]
            Nothing -> Nothing
    tryMatch (PatCon con pats) val =
        case val of
            VCon c args | c == con ->
                let explicitArgs = [a | (Explicit, a) <- args]
                 in if length explicitArgs == length pats then concat <$> zipWithM tryMatch pats explicitArgs else Nothing
            _ -> Nothing
    tryMatch _ _ = Nothing

-- | Semantic function application.
vApp :: Visibility -> Value -> Value -> Value
vApp vis fn arg = case fn of
    VLambda _ _ _ clos ->
        instantiateClosure clos arg
    VCon con args ->
        let allArgs = args ++ [(vis, arg)]
         in case fuseListConstructor con allArgs of
                Just packed -> packed
                Nothing -> VCon con allArgs
    VPrimOp operation args ->
        let newArgs = args ++ [arg]
         in if primitiveArity operation == length newArgs
                 then applyPrimOp operation newArgs
                 else VPrimOp operation newArgs
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
                [_, v] -> evalAbort v
                _ -> VPrimAbort newArgs
    VNeutral fn -> VNeutral (NApp fn vis arg)

fuseListConstructor :: Identifier -> [(Visibility, Value)] -> Maybe Value
fuseListConstructor (Identifier ":") args =
    case [v | (Explicit, v) <- args] of
        [VLit (LitChar c), VLit (LitString s)] -> Just (VLit (LitString (Text.cons c s)))
        [VLit (LitChar c), VCon (Identifier "[]") []] -> Just (VLit (LitString (Text.singleton c)))
        _ -> Nothing
fuseListConstructor _ _ = Nothing

primitiveArity :: PrimOp -> Int
primitiveArity operation = case operation of
    NatToInt -> 1
    IntNeg -> 1
    FloatNeg -> 1
    CharToInt -> 1
    IntToChar -> 1
    StringLength -> 1
    IntToFloat -> 1
    FloatToInt -> 1
    FloatTruncate -> 1
    IntToString -> 1
    FloatToString -> 1
    CharToString -> 1
    StringToList -> 1
    ListToString -> 1
    FloatSqrt -> 1
    FloatSin -> 1
    FloatCos -> 1
    FloatExp -> 1
    FloatLog -> 1
    IntAdd -> 2
    IntSub -> 2
    IntMul -> 2
    IntDiv -> 2
    IntMod -> 2
    IntPow -> 2
    IntEq -> 2
    IntNeq -> 2
    IntLt -> 2
    IntLe -> 2
    IntGt -> 2
    IntGe -> 2
    BoolEq -> 2
    FloatAdd -> 2
    FloatSub -> 2
    FloatMul -> 2
    FloatDiv -> 2
    FloatEq -> 2
    FloatLt -> 2
    FloatLe -> 2
    StringAppend -> 2
    StringEq -> 2
    CharEq -> 2
    IntFold -> 6
    StringIndex -> 2
    StringSlice -> 2

applyPrimOp :: PrimOp -> [Value] -> Value
applyPrimOp operation args = case (operation, args) of
    (IntAdd, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (a + b))
    (IntSub, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (a - b))
    (IntMul, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (a * b))
    (IntDiv, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (a `div` b))
    (IntMod, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (a `mod` b))
    (IntPow, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (a ^ b))
    (IntNeg, [VLit (LitInt a)]) -> VLit (LitInt (-a))
    (IntEq, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a == b then 1 else 0))
    (IntNeq, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a /= b then 1 else 0))
    (IntLt, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a < b then 1 else 0))
    (IntLe, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a <= b then 1 else 0))
    (IntGt, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a > b then 1 else 0))
    (IntGe, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a >= b then 1 else 0))
    (BoolEq, [VLit (LitInt a), VLit (LitInt b)]) -> VLit (LitInt (if a == b then 1 else 0))
    (FloatAdd, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitFloat (a + b))
    (FloatSub, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitFloat (a - b))
    (FloatMul, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitFloat (a * b))
    (FloatDiv, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitFloat (a / b))
    (FloatEq, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitInt (if a == b then 1 else 0))
    (FloatLt, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitInt (if a < b then 1 else 0))
    (FloatLe, [VLit (LitFloat a), VLit (LitFloat b)]) -> VLit (LitInt (if a <= b then 1 else 0))
    (StringAppend, [VLit (LitString a), VLit (LitString b)]) -> VLit (LitString (a <> b))
    (StringEq, [VLit (LitString a), VLit (LitString b)]) -> VLit (LitInt (if a == b then 1 else 0))
    (CharEq, [VLit (LitChar a), VLit (LitChar b)]) -> VLit (LitInt (if a == b then 1 else 0))
    (IntToFloat, [VLit (LitInt a)]) -> VLit (LitFloat (fromInteger a))
    (FloatToInt, [VLit (LitFloat a)]) -> VLit (LitInt (round a))
    (IntToString, [VLit (LitInt n)]) -> VLit (LitString (Text.pack (show n)))
    (FloatToString, [VLit (LitFloat n)]) -> VLit (LitString (Text.pack (show n)))
    (CharToString, [VLit (LitChar c)]) -> VLit (LitString (Text.singleton c))
    (StringLength, [VLit (LitString s)]) -> VLit (LitInt (fromIntegral (Text.length s)))
    (CharToInt, [VLit (LitChar c)]) -> VLit (LitInt (fromIntegral (fromEnum c)))
    (IntToChar, [VLit (LitInt n)]) -> VLit (LitChar (chr (fromInteger n)))
    (StringToList, [VLit (LitString s)]) -> VPrimOp StringToList [VLit (LitString s)]
    (ListToString, [VPrimOp StringToList [VLit (LitString s)]]) -> VLit (LitString s)
    _ -> VPrimOp operation args

evalJ :: Value -> Value -> Value -> Value -> Value -> Value -> Value
evalJ typeA x motiveP baseCaseD y proof = case proof of
    VRefl _ _ | x == y -> baseCaseD
    _ -> VNeutral (NJ typeA x motiveP baseCaseD y (NStuck proof))

evalAbort :: Value -> Value
evalAbort v = VNeutral (NAbort VVoidType (NStuck v))

-- | Quotation: convert a semantic value back to an expression.
quote :: Set Identifier -> Value -> Expression
quote usedVars val = case val of
    VUniverse lvl -> Universe lvl
    VPi vis param dom clos ->
        Pi vis param (quote usedVars dom) (quote (Set.insert param usedVars) (instantiateClosure clos (VNeutral (NVar param))))
    VLambda vis param mType clos ->
        Lambda vis param (fmap (quote usedVars) mType) (quote (Set.insert param usedVars) (instantiateClosure clos (VNeutral (NVar param))))
    VCon con args ->
        foldl (\acc (vis, a) -> Application vis acc (quote usedVars a)) (Variable con) args
    VId a x y ->
        Application Explicit
            (Application Explicit
                (Application Explicit Identity (quote usedVars a))
                (quote usedVars x))
            (quote usedVars y)
    VRefl a x ->
        Application Explicit
            (Application Explicit Reflexivity (quote usedVars a))
            (quote usedVars x)
    VPrimJ args ->
        foldl (Application Explicit) J (map (quote usedVars) args)
    VPrimAbort args ->
        foldl (Application Explicit) Abort (map (quote usedVars) args)
    VPrimIdentity args ->
        foldl (Application Explicit) Identity (map (quote usedVars) args)
    VPrimReflexivity args ->
        foldl (Application Explicit) Reflexivity (map (quote usedVars) args)
    VPrimOp operation args ->
        foldl (Application Explicit) (PrimOp operation) (map (quote usedVars) args)
    VLit lit -> Literal lit
    VPrimType pt -> PrimType pt
    VVoidType -> VoidType
    VNeutral neu -> quoteNeutral usedVars neu
    VUniverse _ -> Universe (UFixed (-1))
    VMetaVar _ -> Hole Nothing
    VHole _ -> Hole Nothing

quoteNeutral :: Set Identifier -> Neutral -> Expression
quoteNeutral usedVars neu = case neu of
    NVar x -> Variable x
    NMetaVar i -> MetaVar i
    NHole _ -> Hole Nothing
    NApp neu vis arg ->
        Application vis (quoteNeutral usedVars neu) (quote usedVars arg)
    NCase target branches env ->
        let quoteBranch (CaseBranch pat rhss _) =
                CaseBranch pat (map quoteRhs rhss) []
            quoteRhs (GuardedRhs guards body) =
                GuardedRhs (map quoteGuard guards) body
            quoteGuard (BoolGuard e) = BoolGuard e
            quoteGuard (PatGuard p e) = PatGuard p e
         in Case (quoteNeutral usedVars target) Nothing (map quoteBranch branches)
    NJ _ _ _ _ _ neu -> quoteNeutral usedVars neu
    NAbort _ neu -> quoteNeutral usedVars neu
    NStuck v -> quote usedVars v
    NPrimOp operation args -> foldl (Application Explicit) (PrimOp operation) (map (quote usedVars) args)

-- | Evaluates an expression to weak head normal form.
evaluateWeakHeadNormalForm :: Environment -> Expression -> Expression
evaluateWeakHeadNormalForm env expr =
    quote (Map.keysSet env `Set.union` freeVariables expr) (evaluate env expr)

-- | Fully normalizes an expression (evaluates under binders).
normalize :: Environment -> Expression -> Expression
normalize env expr =
    quote (Map.keysSet env `Set.union` freeVariables expr) (evaluate env expr)

-- | Definitional equality check with semantic eta-conversion.
areDefinitionallyEqual :: Environment -> Expression -> Expression -> Bool
areDefinitionallyEqual env e1 e2 =
    let v1 = evaluate env e1
        v2 = evaluate env e2
        usedVars =
            Map.keysSet env
                `Set.union` freeVariables e1
                `Set.union` freeVariables e2
     in equalVal usedVars v1 v2

equalVal :: Set Identifier -> Value -> Value -> Bool
equalVal usedVars v1 v2 = case (v1, v2) of
    (VUniverse i, VUniverse j) -> i == j
    (VVoidType, VVoidType) -> True
    (VPrimType t1, VPrimType t2) -> t1 == t2
    (VLit (LitFloat a), VLit (LitFloat b)) -> (isNaN a && isNaN b) || a == b
    (VLit (LitString s), VCon (Identifier "[]") []) -> Text.null s
    (VCon (Identifier "[]") [], VLit (LitString s)) -> Text.null s
    (VLit (LitString s), VCon (Identifier ":") args) -> equalPackedCons usedVars s args
    (VCon (Identifier ":") args, VLit (LitString s)) -> equalPackedCons usedVars s args
    (VLit l1, VLit l2) -> l1 == l2
    (VCon c1 args1, VCon c2 args2) ->
        c1 == c2
            && length args1 == length args2
            && and [vis1 == vis2 && equalVal usedVars a1 a2 | ((vis1, a1), (vis2, a2)) <- zip args1 args2]
    (VPrimOp o1 a1, VPrimOp o2 a2) -> o1 == o2 && equalValList usedVars a1 a2
    (VId a1 x1 y1, VId a2 x2 y2) ->
        equalVal usedVars a1 a2 && equalVal usedVars x1 x2 && equalVal usedVars y1 y2
    (VRefl a1 x1, VRefl a2 x2) ->
        equalVal usedVars a1 a2 && equalVal usedVars x1 x2
    (VPrimIdentity args1, VPrimIdentity args2) ->
        equalValList usedVars args1 args2
    (VPrimReflexivity args1, VPrimReflexivity args2) ->
        equalValList usedVars args1 args2
    (VPrimJ args1, VPrimJ args2) ->
        equalValList usedVars args1 args2
    (VPrimAbort args1, VPrimAbort args2) ->
        equalValList usedVars args1 args2
    (VNeutral (NVar x), VNeutral (NVar y)) -> x == y
    (VNeutral (NMetaVar i), VNeutral (NMetaVar j)) -> i == j
    _ -> False

equalPackedCons :: Set Identifier -> Text -> [(Visibility, Value)] -> Bool
equalPackedCons usedVars s args =
    case (Text.uncons s, [v | (Explicit, v) <- args]) of
        (Just (c, rest), [headVal, tailVal]) ->
            equalVal usedVars (VLit (LitChar c)) headVal
                && equalVal usedVars (VLit (LitString rest)) tailVal
        _ -> False

equalValList :: Set Identifier -> [Value] -> [Value] -> Bool
equalValList _ [] [] = True
equalValList usedVars (a : as) (b : bs) =
    equalVal usedVars a b && equalValList usedVars as bs
equalValList _ _ _ = False
