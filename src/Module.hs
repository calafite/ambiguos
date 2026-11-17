{-# LANGUAGE OverloadedStrings #-}

module Module
    ( ModuleError (..)
    , loadModule
    , loadModuleWithPaths
    ) where

import AST (Expression (..), Statement (..), UniverseLevel (..), Visibility (..))
import AST (Identifier (..))
import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as TextIO
import qualified Data.Text as Text
import Parser (parseProgramWith, defaultFixityEnv)
import System.Directory (doesFileExist)
import System.FilePath ((</>), (<.>), takeExtension)
import TypeChecker (Context (..), checkClassDeclaration, checkDataDeclaration, checkDefinitionWithPartial, checkFunctionDefinitionWithPartial, checkInstanceDeclarationDetailed, checkRecordDeclaration, emptyContext, extendContextDefinition)

data ModuleError
    = ModuleNotFound [FilePath]
    | CircularImport [FilePath]
    | ModuleParseError FilePath
    | ModuleTypeError FilePath
    deriving (Eq, Show)

loadModule :: FilePath -> IO (Either ModuleError Context)
loadModule = loadModuleWithPaths ["."]

loadModuleWithPaths :: [FilePath] -> FilePath -> IO (Either ModuleError Context)
loadModuleWithPaths searchPaths entry = do
    result <- load [] Map.empty entry
    pure (fst result)
  where
    load stack cache requested = do
        pathResult <- resolve requested
        case pathResult of
            Nothing -> pure (Left (ModuleNotFound [requested]), cache)
            Just path
                | path `elem` stack -> pure (Left (CircularImport (reverse (path : stack))), cache)
                | Just ctx <- Map.lookup path cache -> pure (Right ctx, cache)
                | otherwise -> do
                    content <- TextIO.readFile path
                    case parseProgramWith defaultFixityEnv content of
                        Left _ -> pure (Left (ModuleParseError path), cache)
                        Right statements -> do
                            imported <- foldM (loadImport path (path : stack)) (Right emptyContext, cache) statements
                            case imported of
                                (Left err, c) -> pure (Left err, c)
                                (Right base, c) ->
                                    case verify base statements of
                                        Nothing -> pure (Left (ModuleTypeError path), c)
                                        Just ctx -> pure (Right ctx, Map.insert path ctx c)

    loadImport _ _ (Left err, c) _ = pure (Left err, c)
    loadImport _ stack (Right base, c) (ImportStmt _ path _ _) = do
        (result, c') <- load stack c (modulePath path)
        pure (fmap (mergeContexts base) result, c')
    loadImport _ _ state _ = pure state

    verify base statements = foldM step base statements
      where
        step ctx stmt = case stmt of
            DataDeclaration n ps u cs -> either (const Nothing) Just (checkDataDeclaration ctx n ps u cs)
            TypeAlias n ps body ->
                let aliasType = foldr (\(_, p, ty) cod -> Pi Explicit p ty cod) body ps
                    aliasKind = foldr (\(_, p, ty) cod -> Pi Explicit p ty cod) (Universe (UFixed (-1))) ps
                 in Just (extendContextDefinition n aliasKind aliasType ctx)
            RecordDeclaration n ps u fs con -> either (const Nothing) Just (checkRecordDeclaration ctx n ps u fs con)
            Definition partial n ty body -> either (const Nothing) (Just . first3) (checkDefinitionWithPartial partial ctx n ty body)
            FunctionDefinition partial n ty clauses -> either (const Nothing) (Just . first3) (checkFunctionDefinitionWithPartial partial ctx n ty clauses)
            ClassDeclaration n ps _ fs _ -> either (const Nothing) Just (checkClassDeclaration ctx n ps fs)
            InstanceDeclaration n ps h methods -> either (const Nothing) Just (checkInstanceDeclarationDetailed ctx n ps h methods)
            _ -> Just ctx
        first3 (ctx, _, _) = ctx

    mergeContexts a b = Context
        { contextTypes = Map.union (contextTypes a) (contextTypes b)
        , contextValues = Map.union (contextValues a) (contextValues b)
        , contextEnv = Map.union (contextEnv a) (contextEnv b)
        , contextRuntimeEnv = Map.union (contextRuntimeEnv a) (contextRuntimeEnv b)
        , contextLocals = contextLocals a ++ contextLocals b
        , contextData = Map.union (contextData a) (contextData b)
        , contextFixities = Map.union (contextFixities a) (contextFixities b)
        , contextRecords = Map.union (contextRecords a) (contextRecords b)
        , contextInstances = Map.unionWith (++) (contextInstances a) (contextInstances b)
        , contextClassDefaults = Map.union (contextClassDefaults a) (contextClassDefaults b)
        }

    resolve requested = do
        let relative = if takeExtension requested == ".amb" then requested else requested <.> "amb"
            candidates = [ dir </> relative | dir <- searchPaths ]
        existing <- filterM doesFileExist candidates
        pure (case existing of x : _ -> Just x; [] -> Nothing)

    modulePath = foldl (</>) "" . map (Text.unpack . unIdentifier)

    filterM _ [] = pure []
    filterM p (x:xs) = do
        yes <- p x
        rest <- filterM p xs
        pure (if yes then x:rest else rest)
