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
import TypeChecker.Meta (freshMeta, unfoldApp, zonk)
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
    zonkedTargetType <- zonk whnfTargetType
    inferredTargetType <- inferMetaTargetType context zonkedTargetType branches
    let targetType = evaluateWeakHeadNormalForm (contextEnv context) inferredTargetType
    case targetType of
        PrimType pt -> checkPrimitiveCaseBranches checkElab' context pt expType branches
        _ -> checkDataCaseBranches checkElab' context elabTarget targetType expType mMotive branches

inferMetaTargetType :: Context -> Expression -> [CaseBranch] -> Elab Expression
inferMetaTargetType context targetType branches = case targetType of
    MetaVar i -> do
        case firstConstructor branches of
            Just constructor ->
                case findConstructorType constructor (Map.toList (contextData context)) of
                    Just (dataName, info) -> do
                        parameters <- mapM (\(_, _, parameterType) -> freshMeta context parameterType) (dataParams info)
                        let inferred = foldl (Application Explicit) (Variable dataName) parameters
                        unify context (MetaVar i) inferred
                        zonk inferred
                    Nothing -> pure targetType
            Nothing -> case firstLiteral branches of
                Just literal -> do
                    let inferred = literalType literal
                    unify context (MetaVar i) inferred
                    pure inferred
                Nothing -> pure targetType
    _ -> pure targetType
  where
    firstConstructor [] = Nothing
    firstConstructor (CaseBranch (PatCon constructor _) _ _ : _) = Just constructor
    firstConstructor (_ : rest) = firstConstructor rest

    firstLiteral [] = Nothing
    firstLiteral (CaseBranch (PatLit literal) _ _ : _) = Just literal
    firstLiteral (_ : rest) = firstLiteral rest

    findConstructorType _ [] = Nothing
    findConstructorType constructor ((dataName, info) : rest)
        | any ((== constructor) . fst) (dataConstructors info) = Just (dataName, info)
        | otherwise = findConstructorType constructor rest

    literalType (LitInt _) = PrimType PTInt
    literalType (LitFloat _) = PrimType PTFloat
    literalType (LitChar _) = PrimType PTChar
    literalType (LitString _) = Application Explicit (Variable (Identifier "List")) (PrimType PTChar)

checkPrimitiveCaseBranches ::
    (Context -> Expression -> Expression -> Elab Expression) ->
    Context ->
    PrimType ->
    Expression ->
    [CaseBranch] ->
    Elab [CaseBranch]
checkPrimitiveCaseBranches checkElab' context pt expType branches = do
    let defaultSeen = any (\(CaseBranch pat _ _) -> case pat of { PatWild -> True; PatVar _ -> True; _ -> False }) branches
    if not defaultSeen
        then throwError (NonExhaustivePatternMatch (Identifier (Text.pack (show pt))) [Identifier "_"])
        else traverse checkOne branches
  where
    checkOne (CaseBranch pat rhss _) = do
        let body = case rhss of
                GuardedRhs _ rhs : _ -> rhs
                [] -> Hole Nothing
            (effectivePat, branchContext) = case pat of
                PatVar n -> (PatVar n, extendContextType n (PrimType pt) context)
                PatAs n _ -> (PatVar n, extendContextType n (PrimType pt) context)
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
    literalPrimType (LitFloat _) = Just PTFloat
    literalPrimType (LitChar _) = Just PTChar
    literalPrimType (LitString _) = Nothing

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
    let body = case rhss of
            GuardedRhs _ rhs : _ -> rhs
            [] -> Hole Nothing
    let (con, vars) = case pat of
            PatCon c ps -> (c, [case p of { PatVar v -> v; _ -> Identifier ("_pat" <> Text.pack (show i)) } | (i, p) <- zip [(0 :: Int) ..] ps])
            PatVar c -> (c, [])
            PatAs _ _ -> (Identifier "_", [])
            _ -> (Identifier "_", [])
    if con == Identifier "_"
        then do
            let extContext = case pat of
                    PatVar v -> extendContextType v whnfTargetType context
                    PatAs x _ -> extendContextType x whnfTargetType context
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
