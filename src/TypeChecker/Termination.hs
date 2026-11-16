{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Termination
    ( checkPositive
    , checkTermination
    , checkTerminationElab
    ) where

import AST
    ( CaseBranch (..)
    , Expression (..)
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

-- | Strict positivity check: a data type may not occur negatively (bare, as the
-- domain of an arrow) in any of its constructor types. Occurrences applied to
-- variables (parameters/indices) are permitted, since they describe the
-- structural arguments being consumed.
checkPositive :: Identifier -> Expression -> Elab ()
checkPositive dataName expr = go False expr
  where
    go inDomain e = case e of
        Pi _ _ dom codom ->
            go True dom >> go inDomain codom
        Variable ident
            | ident == dataName && inDomain ->
                throwError (NonStrictlyPositive dataName ident)
        Application _ f a ->
            case f of
                Variable ident | ident == dataName -> go inDomain a
                _ -> go inDomain f >> go inDomain a
        Lambda _ _ _ body -> go inDomain body
        Let _ _ d b -> go inDomain d >> go inDomain b
        Case t _mMotive branches ->
            go inDomain t >> mapM_ (go inDomain . branchBody) branches
        Annotation t _ -> go inDomain t
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
            checkBranch' n pp ss gg targetExpr allBranches (CaseBranch pat bdy) =
                let branchGuarded = integerGuard targetExpr allBranches pat gg
                 in checkCalls n pp (Set.union ss (Set.fromList (patternNames pat))) branchGuarded bdy
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
