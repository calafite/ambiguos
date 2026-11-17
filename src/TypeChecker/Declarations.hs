{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Declarations
    ( checkDataDeclaration
    , checkStatement
    , checkRecordDeclaration
    , checkClassDeclaration
    , checkInstanceDeclaration
    , checkInstanceDeclarationDetailed
    , synthesize
    , check
    , checkDefinition
    , checkDefinitionWithPartial
    , checkFunctionDefinition
    , checkFunctionDefinitionWithPartial
    , generalizeType
    , freeTypeVariables
    ) where

import AST
    ( CaseBranch (..)
    , Clause (..)
    , Expression (..)
    , Fixity (..)
    , GuardedRhs (..)
    , Identifier (..)
    , Pattern (..)
    , RecordField (..)
    , RecordInfo (..)
    , Statement (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad (unless)
import Control.Monad.State.Strict (evalStateT)
import Data.Char (isLower)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Evaluation (Value (..))
import PatternMatch (compileClauses)
import Pretty (prettyIdentifier)
import TypeChecker.Elaboration
    ( checkElab
    , synthesizeElab
    )
import TypeChecker.Meta (collectUnsolvedGoals, generalizeInference, zonk)
import TypeChecker.Termination (checkPositive, checkTerminationElab)
import TypeChecker.Types
    ( Context (..)
    , DataInfo (..)
    , ElabState (..)
    , Goal (..)
    , TypeDiagnostic (..)
    , TypeError (..)
    , extendContextDefinition
    , extendContextPartialDefinition
    , extendContextType
    , localTrace
    )
import TypeChecker.Universe
    ( extractUniverseLevel
    , peelIndexTelescope
    , solveUnivConstraints
    )

checkStatement :: Context -> Statement -> Either TypeDiagnostic (Context, [Identifier], [Goal])
checkStatement context statement = case statement of
    DataDeclaration name params universe constructors ->
        withNames (name : map fst constructors) (checkDataDeclaration context name params universe constructors)
    RecordDeclaration name params universe fields constructor ->
        withNames (name : map recordFieldName fields) (checkRecordDeclaration context name params universe fields constructor)
    TypeAlias name params body ->
        let aliasType = foldr (\(_, parameter, parameterType) codomain -> Pi Explicit parameter parameterType codomain) body params
            aliasKind = foldr (\(_, parameter, parameterType) codomain -> Pi Explicit parameter parameterType codomain) (Universe (UFixed (-1))) params
         in Right (extendContextDefinition name aliasKind aliasType context, [name], [])
    Definition partial name maybeType body ->
        withDefinitionName name (checkDefinitionWithPartial partial context name maybeType body)
    FunctionDefinition partial name maybeType clauses ->
        withDefinitionName name (checkFunctionDefinitionWithPartial partial context name maybeType clauses)
    ClassDeclaration name params _ fields _ ->
        withNames [name] (checkClassDeclaration context name params fields)
    InstanceDeclaration className params headType methods ->
        withNames [className] (checkInstanceDeclarationDetailed context className params headType methods)
    Evaluation expression -> do
        (_, _, goals) <- synthesize context expression
        pure (context, [], goals)
    FixityDeclaration associativity precedence operators ->
        let updated = context{contextFixities = foldr (\operator -> Map.insert operator (Fixity associativity precedence)) (contextFixities context) operators}
         in Right (updated, [], [])
    _ -> Right (context, statementNames statement, [])
  where
    withNames names result = do
        updated <- result
        pure (updated, names, [])
    withDefinitionName name result = do
        (updated, _, goals) <- result
        pure (updated, [name], goals)

statementNames :: Statement -> [Identifier]
statementNames statement = case statement of
    FunctionClause (Clause name _ _ _) -> [name]
    _ -> []

checkDataDeclaration ::
    Context ->
    Identifier ->
    [(Visibility, Identifier, Expression)] ->
    Expression ->
    [(Identifier, Expression)] ->
    Either TypeDiagnostic Context
checkDataDeclaration context dataName params univ constructors =
    let traceMsg = "while checking data declaration '" <> prettyIdentifier dataName <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (elabUniv, _) <- synthesizeElab context univ
                    (indices, lvl) <- peelIndexTelescope context elabUniv
                    let allArgs = params ++ indices
                        typeConType = foldr (\(vis, p, ty) codom -> Pi vis p ty codom) (Universe lvl) allArgs
                        contextWithType = extendContextType dataName typeConType context
                        paramContext =
                            foldr
                                (\(_, p, ty) ctx -> extendContextType p ty ctx)
                                contextWithType
                                allArgs
                    (localConstructors, fullConstructors) <-
                        unzip
                            <$> traverse
                                ( \(cName, cType) ->
                                    localTrace
                                        ("while checking constructor '" <> prettyIdentifier cName <> "'")
                                        (checkCon paramContext allArgs (cName, cType))
                                )
                                constructors
                    let dataInfo = DataInfo params indices elabUniv localConstructors
                        finalContext =
                            foldr
                                addConstructor
                                ( contextWithType
                                    { contextData =
                                        Map.insert dataName dataInfo (contextData contextWithType)
                                    }
                                )
                                fullConstructors
                    solveUnivConstraints
                    pure finalContext
            )
            (ElabState 0 Map.empty Map.empty Nothing [] 0 [])
  where
    checkCon pCtx allArgs (cName, cType) = do
        (elabCType, _) <- synthesizeElab pCtx cType
        _ <- checkPositive dataName elabCType
        let fullConType =
                foldr (\(_, p, ty) codom -> Pi Implicit p ty codom) elabCType allArgs
        pure ((cName, elabCType), (cName, fullConType))
    addConstructor (cName, cType) ctx =
        ctx
            { contextTypes = Map.insert cName cType (contextTypes ctx)
            , contextValues = Map.insert cName (Variable cName) (contextValues ctx)
            , contextEnv = Map.insert cName (VCon cName []) (contextEnv ctx)
            , contextRuntimeEnv = Map.insert cName (VCon cName []) (contextRuntimeEnv ctx)
            }

checkRecordDeclaration ::
    Context ->
    Identifier ->
    [(Visibility, Identifier, Expression)] ->
    Expression ->
    [RecordField] ->
    Maybe Identifier ->
    Either TypeDiagnostic Context
checkRecordDeclaration context recName params univ fields mConName =
    let traceMsg = "while checking record declaration '" <> prettyIdentifier recName <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (elabUniv, _) <- synthesizeElab context univ
                    (indices, lvl) <- peelIndexTelescope context elabUniv
                    let allArgs = params ++ indices
                        typeConType = foldr (\(vis, p, ty) codom -> Pi vis p ty codom) (Universe lvl) allArgs
                        contextWithType = extendContextType recName typeConType context
                        paramContext =
                            foldr
                                (\(_, p, ty) ctx -> extendContextType p ty ctx)
                                contextWithType
                                allArgs
                    let conName = fromMaybe (Identifier ("mk" <> unIdentifier recName)) mConName
                        conAppArgs = map (\(_, p, _) -> Variable p) allArgs
                        conApp = foldl (\acc x -> Application Explicit acc x) (Variable recName) conAppArgs
                        conRawType =
                            foldr
                                (\field acc -> Pi Explicit (recordFieldName field) (recordFieldType field) acc)
                                conApp
                                fields
                    _ <- checkPositive recName conRawType
                    (elabConType, _) <- synthesizeElab paramContext conRawType
                    let fullConType =
                            foldr (\(_, p, ty) codom -> Pi Implicit p ty codom) elabConType allArgs
                        conVars = map recordFieldName fields
                        projectionFor field =
                            let recVar = Identifier "record"
                                branch = CaseBranch (PatCon conName (map PatVar conVars)) [GuardedRhs [] (Variable (recordFieldName field))] []
                                body = Lambda Explicit recVar Nothing (Case (Variable recVar) Nothing [branch])
                                value = foldr (\(_, p, _) b -> Lambda Implicit p Nothing b) body allArgs
                                ty = foldr (\(_, p, t) b -> Pi Implicit p t b)
                                         (Pi Explicit recVar (foldl (Application Explicit) (Variable recName) conAppArgs) (recordFieldType field))
                                         allArgs
                             in (recordFieldName field, ty, value)
                        projectionBindings = map projectionFor fields
                        ctxWithCon =
                            paramContext
                                { contextTypes = Map.insert conName fullConType (contextTypes paramContext)
                                , contextValues = Map.insert conName (Variable conName) (contextValues paramContext)
                                , contextEnv = Map.insert conName (VCon conName []) (contextEnv paramContext)
                                , contextRuntimeEnv = Map.insert conName (VCon conName []) (contextRuntimeEnv paramContext)
                                }
                        ctxWithProjections =
                            foldr (\(fieldName, fieldType, fieldValue) ctx ->
                                    extendContextDefinition fieldName fieldType fieldValue ctx)
                                  ctxWithCon projectionBindings
                    let recInfo =
                            RecordInfo
                                { recordName = recName
                                , recordParams = params
                                , recordUniverse = elabUniv
                                , recordFields = fields
                                , recordConName = conName
                                }
                        finalContext =
                            stripRecordParameters (map (\(_, p, _) -> p) allArgs) context ctxWithProjections
                                { contextRecords =
                                    Map.insert recName recInfo (contextRecords ctxWithCon)
                                }
                    solveUnivConstraints
                    pure finalContext
            )
            (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

stripRecordParameters :: [Identifier] -> Context -> Context -> Context
stripRecordParameters parameters outer inner =
    inner
        { contextTypes = restore contextTypes
        , contextValues = restore contextValues
        , contextEnv = restore contextEnv
        , contextRuntimeEnv = restore contextRuntimeEnv
        , contextLocals = contextLocals outer
        }
  where
    restore getter = foldr (restoreOne getter) (getter inner) parameters
    restoreOne getter name current =
        case Map.lookup name (getter outer) of
            Just original -> Map.insert name original current
            Nothing -> Map.delete name current

checkClassDeclaration :: Context -> Identifier -> [(Visibility, Identifier, Expression)] -> [RecordField] -> Either TypeDiagnostic Context
checkClassDeclaration context name params fields =
    checkRecordDeclaration context name params (Universe (UFixed (-1))) fields Nothing

checkInstanceDeclarationDetailed :: Context -> Identifier -> [(Visibility, Identifier, Expression)] -> Expression -> [(Identifier, [Clause])] -> Either TypeDiagnostic Context
checkInstanceDeclarationDetailed context className _params headType methods = do
    case Map.lookup className (contextRecords context) of
        Nothing -> Left (TypeDiagnostic Nothing [] (UnboundVariable className))
        Just _info ->
            let supplied = [(name, compileClauses Nothing clauses) | (name, clauses) <- methods]
             in checkInstanceDeclaration context className headType supplied

checkInstanceDeclaration :: Context -> Identifier -> Expression -> [(Identifier, Expression)] -> Either TypeDiagnostic Context
checkInstanceDeclaration context className headType fields = do
    info <- case Map.lookup className (contextRecords context) of
        Just x -> Right x
        Nothing -> Left (TypeDiagnostic Nothing [] (UnboundVariable className))
    let instanceName = Identifier ("instance_" <> unIdentifier className <> "_" <> Text.pack (show headType))
        supplied = Map.fromList fields
        defaults = Map.fromList (Map.findWithDefault [] className (contextClassDefaults context))
        ordered = traverse (\f -> case Map.lookup (recordFieldName f) supplied of
                Just value -> Right value
                Nothing -> maybe (Left (TypeDiagnostic Nothing [] (UnknownField (recordFieldName f) className))) Right (Map.lookup (recordFieldName f) defaults)) (recordFields info)
    values <- ordered
    let instanceType =
            case headType of
                Pi Instance _ _ _ -> headType
                _ -> Application Explicit (Variable className) headType
        dict = foldl (Application Explicit) (Variable (recordConName info)) values
    (updated, _, _) <- checkDefinition context instanceName (Just instanceType) dict
    Right updated { contextInstances = Map.insertWith (++) className [instanceName] (contextInstances updated) }

synthesize :: Context -> Expression -> Either TypeDiagnostic (Expression, Expression, [Goal])
synthesize context rawExpr =
    evalStateT
        ( do
            (elabExpr, rawType) <- synthesizeElab context rawExpr
            zonkedType <- zonk rawType
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            solveUnivConstraints
            pure (zonkedExpr, zonkedType, goals)
        )
        (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

check :: Context -> Expression -> Expression -> Either TypeDiagnostic (Expression, [Goal])
check context rawExpr expType =
    evalStateT
        ( do
            (elabExpected, _) <- synthesizeElab context expType
            zonkedExpected <- zonk elabExpected
            elabExpr <- checkElab context rawExpr zonkedExpected
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            solveUnivConstraints
            pure (zonkedExpr, goals)
        )
        (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

checkDefinition ::
    Context ->
    Identifier ->
    Maybe Expression ->
    Expression ->
    Either TypeDiagnostic (Context, Expression, [Goal])
checkDefinition context name maybeDeclaredType bodyTerm =
    checkDefinitionWithPartial False context name maybeDeclaredType bodyTerm

checkDefinitionWithPartial ::
    Bool ->
    Context ->
    Identifier ->
    Maybe Expression ->
    Expression ->
    Either TypeDiagnostic (Context, Expression, [Goal])
checkDefinitionWithPartial isPartial context name maybeDeclaredType bodyTerm =
    let traceMsg = "while checking definition '" <> prettyIdentifier name <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (zonkedBody, finalType) <-
                        case maybeDeclaredType of
                            Just declaredType -> do
                                let generalizedType = generalizeType context declaredType
                                (elabDeclType, typeUniverse) <- synthesizeElab context generalizedType
                                _ <- extractUniverseLevel context typeUniverse
                                zonkedDeclType <- zonk elabDeclType
                                -- The name is in scope for its own body (so it can
                                -- refer to itself recursively), but only in
                                -- contextTypes, not contextValues, so it stays
                                -- neutral during typechecking and cannot diverge
                                -- the elaboration.
                                let recursiveContext = extendContextType name elabDeclType context
                                elabBody <- checkElab recursiveContext bodyTerm zonkedDeclType
                                zonkedBodyTerm <- zonk elabBody
                                unless isPartial (checkTerminationElab name zonkedBodyTerm)
                                zonkedFinalType <- zonk zonkedDeclType
                                pure (zonkedBodyTerm, zonkedFinalType)
                            Nothing -> do
                                (elabBody, rawType) <- synthesizeElab context bodyTerm
                                zonkedType <- zonk rawType
                                zonkedBodyTerm <- zonk elabBody
                                unless isPartial (checkTerminationElab name zonkedBodyTerm)
                                zonkedFinalType <- zonk zonkedType
                                pure (zonkedBodyTerm, zonkedFinalType)
                    (finalBody, generalizedType) <-
                        if maybeDeclaredType == Nothing
                            then generalizeInference context zonkedBody finalType
                            else pure (zonkedBody, finalType)
                    goals <- collectUnsolvedGoals
                    solveUnivConstraints
                    let updatedContext =
                            if isPartial
                                then extendContextPartialDefinition name generalizedType finalBody context
                                else extendContextDefinition name generalizedType finalBody context
                    pure (updatedContext, generalizedType, goals)
            )
            (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

checkFunctionDefinition :: Context -> Identifier -> Maybe Expression -> [Clause] -> Either TypeDiagnostic (Context, Expression, [Goal])
checkFunctionDefinition context name maybeDeclaredType clauses =
    checkFunctionDefinitionWithPartial False context name maybeDeclaredType clauses

checkFunctionDefinitionWithPartial :: Bool -> Context -> Identifier -> Maybe Expression -> [Clause] -> Either TypeDiagnostic (Context, Expression, [Goal])
checkFunctionDefinitionWithPartial isPartial context name maybeDeclaredType clauses =
    case clauses of
        [] -> Left (TypeDiagnostic Nothing [] (CannotSynthesizeType (Variable name)))
        firstClause : _
            | any ((/= length (clausePats firstClause)) . length . clausePats) clauses ->
                Left (TypeDiagnostic Nothing [] (ArityMismatch name (length (clausePats firstClause)) (length (clausePats firstClause))))
            | otherwise ->
                let generalizedType = fmap (generalizeType context) maybeDeclaredType
                 in checkDefinitionWithPartial isPartial context name generalizedType (compileClauses generalizedType clauses)

generalizeType :: Context -> Expression -> Expression
generalizeType context signature =
    foldr (\ident body -> Pi Implicit ident (Universe (UFixed (-1))) body)
        signature
        (freeTypeVariables context signature)

freeTypeVariables :: Context -> Expression -> [Identifier]
freeTypeVariables context expression =
    List.nub [ident | ident <- orderedFreeVars expression, isCandidate ident]
  where
    isCandidate ident@(Identifier name) =
        case Text.uncons name of
            Just (firstChar, _) -> isLower firstChar && Map.notMember ident (contextTypes context)
            Nothing -> False

    orderedFreeVars expr = case expr of
        Variable ident -> [ident]
        Pi _ parameter domain codomain ->
            orderedFreeVars domain ++ filter (/= parameter) (orderedFreeVars codomain)
        Application _ function argument -> orderedFreeVars function ++ orderedFreeVars argument
        Annotation term ty -> orderedFreeVars term ++ orderedFreeVars ty
        Tuple terms -> concatMap orderedFreeVars terms
        Located _ inner -> orderedFreeVars inner
        _ -> []
