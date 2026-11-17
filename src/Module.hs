{-# LANGUAGE OverloadedStrings #-}

module Module
    ( ModuleError (..)
    , loadModule
    , loadModuleWithPaths
    ) where

import AST (Statement (..))
import AST (Identifier (..))
import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Text.IO as TextIO
import qualified Data.Text as Text
import Parser (parseProgramWith, defaultFixityEnv)
import System.Directory (doesFileExist)
import System.FilePath ((</>), (<.>), takeExtension)
import TypeChecker (Context (..), checkStatement, emptyContext)

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
                                        Left _ -> pure (Left (ModuleTypeError path), c)
                                        Right ctx -> pure (Right ctx, Map.insert path ctx c)

    loadImport _ _ (Left err, c) _ = pure (Left err, c)
    loadImport _ stack (Right base, c) (ImportStmt _ path _ _) = do
        (result, c') <- load stack c (modulePath path)
        pure (fmap (mergeContexts base) result, c')
    loadImport _ _ state _ = pure state

    verify base statements = foldM step base statements
      where
        step ctx stmt = fmap (\(updated, _, _) -> updated) (checkStatement ctx stmt)

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
