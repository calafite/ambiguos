{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.PatternCheck
    ( peelConstructorArgs
    , isConNonAbsurd
    , extractConIndexArgs
    , unifyIndexArgs
    , checkCaseBranches
    , checkPrimitiveCaseBranches
    , checkDataCaseBranches
    , checkBranch
    , checkConstructorBranch
    ) where

import AST
    ( CaseBranch (..)
    , Expression (..)
    , GuardedRhs (..)
    , Identifier (..)
    , Literal (..)
    , Pattern (..)
    , PrimType (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad (filterM)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Evaluation (evaluateWeakHeadNormalForm)
import Substitution (substitute)
import TypeChecker.Meta (freshMeta, unfoldApp)
import TypeChecker.Types
    ( Context (..)
    , DataInfo (..)
    , Elab
    , TypeError (..)
    , catchElab
    , extendContextDefinition
    , extendContextType
    , throwError
    )
import TypeChecker.Unify (unify)

checkCaseBranches ::
    (Context -> Expression -> Expression -> Elab Expression) ->
    Context ->
    Expression ->
    Expression ->
    Expression ->
    Maybe (Identifier, Expression) ->
    [CaseBranch] ->
    Elab [CaseBranch]
checkCaseBranches checkElab' context elabTarget whnfTargetType expType mMotive branches = do
    case whnfTargetType of
        PrimType pt -> checkPrimitiveCaseBranches checkElab' context pt expType branches
        _ -> checkDataCaseBranches checkElab' context elabTarget whnfTargetType expType mMotive branches

checkPrimitiveCaseBranches ::
    (Context -> Expression -> Expression -> Elab Expression) ->
    Context ->
    PrimType ->
    Expression ->
    [CaseBranch] ->
    Elab [CaseBranch]
checkPrimitiveCaseBranches checkElab' context pt expType branches = do
    let defaultSeen = any (\(CaseBranch pat _ _) -> case pat of { PatWild -> True; PatVar _ -> True; PatCon _ [] -> True; _ -> False }) branches
    if not defaultSeen
        then throwError (NonExhaustivePatternMatch (Identifier (Text.pack (show pt))) [Identifier "_"])
        else traverse checkOne branches
  where
    checkOne (CaseBranch pat rhss _) = do
        let body = guardedRhsBody (head rhss)
            (effectivePat, branchContext) = case pat of
                PatCon n [] -> (PatVar n, extendContextType n (PrimType pt) context)
                PatVar n -> (PatVar n, extendContextType n (PrimType pt) context)
                PatWild -> (PatWild, context)
                PatLit (LitInt n) | pt == PTInt -> (PatLit (LitInt n), context)
                PatLit (LitInt n) | pt == PTFloat -> (PatLit (LitFloat (fromIntegral n)), context)
                PatLit lit -> (PatLit lit, context)
                _ -> (pat, context)
        case effectivePat of
            PatLit lit | literalPrimType lit /= Just pt -> throwError (TypeMismatch (PrimType pt) (literalType lit))
            PatCon _ _ -> throwError (CannotMatchOnNonDataType (PrimType pt))
            _ -> pure ()
        elabBody <- checkElab' branchContext body expType
        pure (CaseBranch effectivePat [GuardedRhs [] elabBody] [])
    literalType (LitInt _) = PrimType PTInt
    literalType (LitFloat _) = PrimType PTFloat
    literalType (LitChar _) = PrimType PTChar
    literalType (LitString _) = Application Explicit (Variable (Identifier "List")) (PrimType PTChar)
    literalPrimType (LitInt _) = Just PTInt
    literalPrimType (LitInt _) = Just PTInt
    literalPrimType (LitFloat _) = Just PTFloat
    literalPrimType (LitChar _) = Just PTChar

checkDataCaseBranches ::
    (Context -> Expression -> Expression -> Elab Expression) ->
    Context ->
    Expression ->
    Expression ->
    Expression ->
    Maybe (Identifier, Expression) ->
    [CaseBranch] ->
    Elab [CaseBranch]
checkDataCaseBranches checkElab' context elabTarget whnfTargetType expType mMotive branches = do
    let (headExpr, typeArgs) = unfoldApp whnfTargetType
    dataTypeName <- case headExpr of
        Variable ident -> pure ident
        VoidType -> pure (Identifier "Void")
        other -> throwError (CannotMatchOnNonDataType other)
    dataInfo <- case Map.lookup dataTypeName (contextData context) of
        Just info -> pure info
        Nothing -> throwError (CannotMatchOnNonDataType headExpr)
    let numParams = length (dataParams dataInfo)
        (paramArgs, indexArgs) = splitAt numParams typeArgs
        paramArgsExprs = map snd paramArgs
        indexArgsExprs = map snd indexArgs
        expectedConstructors = map fst (dataConstructors dataInfo)
    expectedNonAbsurd <-
        filterM
            ( \cName ->
                isConNonAbsurd
                    context
                    dataInfo
                    paramArgsExprs
                    indexArgsExprs
                    dataTypeName
                    cName
            )
            expectedConstructors
    let branchConstructors = [c | CaseBranch (PatCon c _) _ _ <- branches]
        hasDefault = any (\(CaseBranch p _ _) -> case p of { PatWild -> True; PatVar _ -> True; _ -> False }) branches
        missingConstructors =
            filter (`notElem` branchConstructors) expectedNonAbsurd
    if not hasDefault && not (null missingConstructors) && dataTypeName /= Identifier "Void"
        then throwError (NonExhaustivePatternMatch dataTypeName missingConstructors)
        else traverse
            ( checkBranch
                checkElab'
                context
                elabTarget
                dataInfo
                paramArgsExprs
                indexArgsExprs
                dataTypeName
                whnfTargetType
                mMotive
                expType
            )
            branches

isConNonAbsurd ::
    Context ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Identifier ->
    Elab Bool
isConNonAbsurd context dataInfo paramArgs indexArgs dataTypeName cName = do
    localConType <-
        case lookup cName (dataConstructors dataInfo) of
            Just ty -> pure ty
            Nothing -> throwError (UnknownConstructor dataTypeName cName)
    conIndexArgs <- extractConIndexArgs context localConType paramArgs dataTypeName
    case conIndexArgs of
        Just cargs -> do
            result <-
                catchElab
                    ( unifyIndexArgs context cargs indexArgs >> pure True
                    )
                    (const (pure False))
            pure result
        Nothing -> pure False

extractConIndexArgs ::
    Context -> Expression -> [Expression] -> Identifier -> Elab (Maybe [Expression])
extractConIndexArgs context expr paramArgs dataTypeName = do
    let env = contextEnv context
        w = evaluateWeakHeadNormalForm env expr
    case w of
        Pi _ _ _ codom -> extractConIndexArgs context codom paramArgs dataTypeName
        VoidType | dataTypeName == Identifier "Void" -> pure (Just [])
        other ->
            let (headExpr, allArgs) = unfoldApp other
             in case headExpr of
                    Variable dt
                        | dt == dataTypeName ->
                            let numParams = length paramArgs
                                (_, cargs) = splitAt numParams allArgs
                             in pure (Just (map snd cargs))
                    _ -> pure Nothing

unifyIndexArgs :: Context -> [Expression] -> [Expression] -> Elab ()
unifyIndexArgs _ [] [] = pure ()
unifyIndexArgs context (c : cs) (t : ts) = do
    unify context c t
    unifyIndexArgs context cs ts
unifyIndexArgs _ _ _ = pure ()

checkBranch ::
    (Context -> Expression -> Expression -> Elab Expression) ->
    Context ->
    Expression ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Expression ->
    Maybe (Identifier, Expression) ->
    Expression ->
    CaseBranch ->
    Elab CaseBranch
checkBranch checkElab' context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType (CaseBranch pat rhss _) = do
    let body = guardedRhsBody (head rhss)
    let (con, vars) = case pat of
            PatCon c ps -> (c, [case p of { PatVar v -> v; _ -> Identifier ("_pat" <> Text.pack (show i)) } | (i, p) <- zip [(0 :: Int) ..] ps])
            PatVar c -> (c, [])
            _ -> (Identifier "_", [])
    if con == Identifier "_"
        then do
            let extContext = case pat of
                    PatVar v -> extendContextType v whnfTargetType context
                    _ -> context
            elabBody <- checkElab' extContext body expType
            pure (CaseBranch pat [GuardedRhs [] elabBody] [])
        else do
            checked <- checkConstructorBranch checkElab' context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType con vars body
            pure checked { branchPattern = pat }

checkConstructorBranch ::
    (Context -> Expression -> Expression -> Elab Expression) ->
    Context ->
    Expression ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Expression ->
    Maybe (Identifier, Expression) ->
    Expression ->
    Identifier ->
    [Identifier] ->
    Expression ->
    Elab CaseBranch
checkConstructorBranch checkElab' context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType con vars body = do
    localConType <-
        case lookup con (dataConstructors dataInfo) of
            Just ty -> pure ty
            Nothing -> throwError (UnknownConstructor dataTypeName con)
    let paramNames = map (\(_, p, _) -> p) (dataParams dataInfo)
        conSubst = foldr (\(p, a) acc -> substitute p a acc) localConType (zip paramNames paramArgs)
    (explicitArgTypes, _) <- peelConstructorArgs context vars conSubst
    fallbackArgTypes <- mapM (\_ -> freshMeta context (Universe (UFixed (-1)))) (drop (length explicitArgTypes) vars)
    let allArgTypes = explicitArgTypes ++ fallbackArgTypes
    let extContext =
            foldr (\(v, ty) ctx -> extendContextType v ty ctx) context (zip vars allArgTypes)
        conApp =
            foldl
                (Application Explicit)
                (foldl
                    (Application Implicit)
                    (Variable con)
                    indexArgs
                )
                (map Variable vars)
        (refContext, branchExpected) =
            case (elabTarget, mMotive) of
                (Variable targetVar, Just (mv, mtype)) ->
                    ( extendContextDefinition targetVar whnfTargetType conApp extContext
                    , substitute targetVar conApp (substitute mv conApp mtype)
                    )
                (Variable targetVar, Nothing) ->
                    ( extendContextDefinition targetVar whnfTargetType conApp extContext
                    , substitute targetVar conApp expType
                    )
                (_, Just (mv, mtype)) ->
                    (extContext, substitute mv conApp mtype)
                _ -> (extContext, expType)
    elabBody <- checkElab' refContext body branchExpected
    pure (CaseBranch (PatCon con (map PatVar vars)) [GuardedRhs [] elabBody] [])

peelConstructorArgs :: Context -> [Identifier] -> Expression -> Elab ([Expression], Expression)
peelConstructorArgs _ [] ty = pure ([], ty)
peelConstructorArgs ctx (v : vs) ty = do
    let env = contextEnv ctx
        wTy = evaluateWeakHeadNormalForm env ty
    case wTy of
        Pi Explicit param dom codom -> do
            (rest, finalCodom) <- peelConstructorArgs ctx vs (substitute param (Variable v) codom)
            pure (dom : rest, finalCodom)
        Pi Implicit param _ codom -> do
            m <- freshMeta ctx (Universe (UFixed (-1)))
            peelConstructorArgs ctx (v : vs) (substitute param m codom)
        Pi Instance param _ codom -> do
            m <- freshMeta ctx (Universe (UFixed (-1)))
            peelConstructorArgs ctx (v : vs) (substitute param m codom)
        other ->
            throwError (ExpectedFunctionType other)

{- Dead legacy compiler retained temporarily for source compatibility history.
compilePatternCase ::
    (Context -> Expression -> Elab (Expression, Expression)) ->
    Context ->
    Expression ->
    [(Pattern, Expression)] ->
    Elab [CaseBranch]
compilePatternCase synElab context target clauses = do
    (_, targetType) <- synElab context target
    let (headType, _) = unfoldApp targetType
        constructors = case headType of
            Variable name -> maybe [] (map fst . dataConstructors) (Map.lookup name (contextData context))
            _ -> []
        constructorArity name = case Map.lookup name (contextData context) >>= lookup name . dataConstructors of
            Nothing -> 0
            Just ty -> countExplicit ty
        countExplicit ty = case evaluateWeakHeadNormalForm (contextEnv context) ty of
            Pi Explicit _ _ codom -> 1 + countExplicit codom
            Pi _ _ _ codom -> countExplicit codom
            _ -> 0
        freshArgs name = [Identifier ("pat" <> Text.pack (show (i :: Int))) | i <- [0 .. constructorArity name - 1]]
        expandWild body =
            [ CaseBranch (PatCon con (map PatVar (freshArgs con))) [GuardedRhs [] body] [] | con <- constructors ]
        literalPattern n
            | n <= 0 = PatCon (Identifier "zero") []
            | otherwise = PatCon (Identifier "successor") [literalPattern (n - 1)]
        tuplePattern [] = PatCon (Identifier "unit") []
        tuplePattern [p] = p
        tuplePattern (p : ps) = PatCon (Identifier "pair") [p, tuplePattern ps]
        compileAt scrutinee pattern body = case pattern of
            PatVar name -> Let name Nothing scrutinee body
            PatWild -> body
            PatLit (LitInt n) -> compileAt scrutinee (literalPattern n) body
            PatTuple ps -> compileAt scrutinee (tuplePattern ps) body
            PatCon con subpatterns ->
                let args = [Identifier ("pat" <> Text.pack (show (i :: Int))) | i <- [0 .. length subpatterns - 1]]
                    nested = foldr (\(arg, subpattern) acc -> compileAt (Variable arg) subpattern acc) body (zip args subpatterns)
                 in Case scrutinee Nothing [CaseBranch (PatCon con (map PatVar args)) [GuardedRhs [] nested] []]
            PatLit _ -> body
        compileTop pattern body = case pattern of
            PatVar name -> expandWild (substitute name target body)
            PatWild -> expandWild body
            PatLit (LitInt n) -> compileTop (literalPattern n) body
            PatTuple ps -> compileTop (tuplePattern ps) body
            PatCon con subpatterns ->
                let args = [Identifier ("pat" <> Text.pack (show (i :: Int))) | i <- [0 .. length subpatterns - 1]]
                    nested = foldr (\(arg, subpattern) acc -> compileAt (Variable arg) subpattern acc) body (zip args subpatterns)
                 in [CaseBranch (PatCon con (map PatVar args)) [GuardedRhs [] nested] []]
            PatLit _ -> expandWild body
    pure (concatMap (uncurry compileTop) clauses)
-}
