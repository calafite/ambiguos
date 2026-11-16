{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Termination
    ( checkPositive
    , checkTermination
    , checkTerminationElab
    ) where

import AST
    ( CaseBranch (..)
    , Expression (..)
    , GuardedRhs (..)
    , Identifier (..)
    , Literal (..)
    , Pattern (..)
    , PrimOp (..)
    , Visibility (..)
    )
import qualified Data.Set as Set
import Substitution (freeVariables)
import TypeChecker.Meta (stripLocated, unfoldApp)
import TypeChecker.Types
    ( Elab
    , TypeError (..)
    , throwError
    )

-- | Strict positivity check for a constructor type.
--
-- The outer Pi telescope is the constructor's list of fields, so a recursive
-- type is allowed there: @Succ :: Nat -> Nat@ is the canonical example.  Pi
-- types nested inside a field are actual function types, however, and their
-- domains are negative: @Bad :: (Bad -> Int) -> Bad@ must be rejected.
checkPositive :: Identifier -> Expression -> Elab ()
checkPositive dataName expr = checkFields expr
  where
    checkFields (Pi _ _ field rest) = checkPositiveField field >> checkFields rest
    checkFields _ = pure ()

    checkPositiveField = goPositive

    goPositive e = case e of
        Variable ident
            | ident == dataName -> pure ()
        Pi _ _ dom codom -> goNegative dom >> goPositive codom
        Application _ f a ->
            goPositive f >> goPositive a
        Lambda _ _ _ body -> goPositive body
        Let _ _ d b -> goPositive d >> goPositive b
        Case t _mMotive branches ->
            goPositive t >> mapM_ (goPositive . branchBody) branches
          where
            branchBody (CaseBranch _ rhss _) = guardedRhsBody (head rhss)
        Annotation t _ -> goPositive t
        _ -> pure ()

    goNegative e = case e of
        Variable ident
            | ident == dataName ->
                throwError (NonStrictlyPositive dataName ident)
        Pi _ _ dom codom -> goPositive dom >> goNegative codom
        Application _ f a -> goNegative f >> goNegative a
        Lambda _ _ _ body -> goNegative body
        Let _ _ d b -> goNegative d >> goNegative b
        Case t _mMotive branches ->
            goNegative t >> mapM_ (goNegative . branchBody) branches
          where
            branchBody (CaseBranch _ rhss _) = guardedRhsBody (head rhss)
        Annotation t _ -> goNegative t
        _ -> pure ()

-- | Structural termination check: every recursive call to `name` must apply at
-- least one argument that is a structurally smaller variable (a constructor
-- subterm obtained by pattern matching on a parameter). Variables bound by the
-- function's own lambda parameters are tracked as `params`; variables bound by
-- case patterns on a parameter are tracked as `small` (strictly smaller).
checkTermination :: Identifier -> Expression -> Either TypeError ()
checkTermination name body =
    if Set.member name (freeVariables body)
        then checkCalls name Set.empty Set.empty Set.empty body
        else pure ()
  where
    checkCalls :: Identifier -> Set.Set Identifier -> Set.Set Identifier -> Set.Set Identifier -> Expression -> Either TypeError ()
    checkCalls nm params small guarded expr = case expr of
        Lambda _ pname _ bdy ->
            checkCalls nm (Set.insert pname params) small guarded bdy
        Case target _mMotive branches ->
            let targetVar = case target of Variable v -> Just v; _ -> Nothing
                small' = case targetVar of
                    Just v
                        | Set.member v params || Set.member v small ->
                            Set.union small (Set.fromList (concatMap (patternNames . branchPattern) branches))
                    _ -> small
             in mapM_ (checkBranch' nm params small' guarded target branches) branches
          where
            checkBranch' n pp ss gg targetExpr allBranches (CaseBranch pat rhss _) =
                let branchGuarded = integerGuard targetExpr allBranches pat gg
                 in checkCalls n pp (Set.union ss (Set.fromList (patternNames pat))) branchGuarded (guardedRhsBody (head rhss))
            patternNames (PatVar v) = [v]
            patternNames PatWild = []
            patternNames (PatLit _) = []
            patternNames (PatCon _ ps) = concatMap patternNames ps
            patternNames (PatTuple ps) = concatMap patternNames ps
        Application _ f arg ->
            let (h, spine) = unfoldApp expr
             in case h of
                    Variable ident | ident == nm ->
                        if any (\(_, a) -> isSmallerArgument params small guarded a) spine
                            then mapM_ (checkCalls nm params small guarded . snd) spine >> pure ()
                            else Left (NonTerminatingDefinition nm)
                    _ -> checkCalls nm params small guarded f >> checkCalls nm params small guarded arg
        Pi _ _ dom codom ->
            checkCalls nm params small guarded dom >> checkCalls nm params small guarded codom
        Let _ _ d b ->
            checkCalls nm params small guarded d >> checkCalls nm params small guarded b
        Annotation t _ -> checkCalls nm params small guarded t
        _ -> pure ()

    isSmallerArgument params small guarded argument =
        case argument of
            Variable v -> Set.member v small
            _ ->
                let (headExpr, arguments) = unfoldApp argument
                    explicitArguments = [value | (Explicit, value) <- arguments]
                 in case (headExpr, reverse explicitArguments) of
                        (Variable (Identifier "drop"), Variable v : _) -> Set.member v (Set.union params small)
                        _ -> False
                    || case (headExpr, explicitArguments) of
                        (PrimOp IntSub, [Variable v, Literal (LitInt k)]) ->
                            k >= 1 && Set.member v guarded
                        _ -> False

    integerGuard target branches pattern guards =
        case (stripLocated target, pattern) of
            (Application Explicit (Application Explicit (PrimOp IntLe) (Variable v)) (Literal (LitInt _)), PatCon con [])
                | con == Identifier "false" -> Set.insert v guards
            (Variable v, PatWild)
                | any (isPositiveBase . branchPattern) branches -> Set.insert v guards
            (Variable v, PatVar _)
                | any (isPositiveBase . branchPattern) branches -> Set.insert v guards
            _ -> guards

    isPositiveBase (PatLit (LitInt n)) = n >= 0
    isPositiveBase _ = False

checkTerminationElab :: Identifier -> Expression -> Elab ()
checkTerminationElab nm b = case checkTermination nm b of
    Left err -> throwError err
    Right () -> pure ()
