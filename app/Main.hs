{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import AST (Identifier (..), Statement (..))
import qualified Control.Exception as Exception
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Evaluation (normalize)
import Parser (parseProgram, parseStatement, renderParseError)
import Pretty (prettyExpression, prettyIdentifier)
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
import TypeChecker
  ( Context (..)
  , checkDefinition
  , emptyContext
  , renderTypeError
  , synthesize
  )

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do
      putStrLn "Ambiguos Formal Verification System"
      putStrLn "Commands: def <name> : <Type> = <term> | <expr> | :load <file> | quit"
      replLoop emptyContext

    [filePath] -> do
      putStrLn ("Verifying file: " ++ filePath)
      result <- loadFile emptyContext filePath
      case result of
        Just contextWithFile -> do
          putStrLn "All definitions verified successfully. Entering interactive REPL..."
          replLoop contextWithFile
        Nothing ->
          putStrLn "Verification failed. Terminating."

    _ ->
      putStrLn "Usage: ambiguos [file.amb]"

replLoop :: Context -> IO ()
replLoop context = do
  putStr "> "
  hFlush stdout
  rawInput <- TextIO.getLine
  case rawInput of
    "quit" -> putStrLn "Terminating session."

    _ | Text.isPrefixOf ":load " rawInput || Text.isPrefixOf ":l " rawInput -> do
          let filePath = Text.unpack (Text.strip (Text.dropWhile (/= ' ') rawInput))
          maybeUpdatedContext <- loadFile context filePath
          case maybeUpdatedContext of
            Just newContext -> replLoop newContext
            Nothing         -> replLoop context

      | otherwise -> do
          case parseStatement rawInput of
            Left parseError -> do
              TextIO.putStrLn (renderParseError parseError)
              replLoop context

            Right (Definition name declaredType bodyTerm) ->
              case checkDefinition context name declaredType bodyTerm of
                Left typeError -> do
                  TextIO.putStrLn ("Type Error: " <> renderTypeError typeError)
                  replLoop context
                Right updatedContext -> do
                  TextIO.putStrLn
                    ( "Defined '"
                        <> prettyIdentifier name
                        <> "' with type "
                        <> prettyExpression declaredType
                        <> "."
                    )
                  replLoop updatedContext

            Right (Evaluation expression) -> do
              case synthesize context expression of
                Left typeError ->
                  TextIO.putStrLn ("Type Error: " <> renderTypeError typeError)
                Right inferredType -> do
                  let values = contextValues context
                  TextIO.putStrLn ("Type:       " <> prettyExpression (normalize values inferredType))
                  TextIO.putStrLn ("Normalized: " <> prettyExpression (normalize values expression))
              replLoop context

loadFile :: Context -> FilePath -> IO (Maybe Context)
loadFile initialContext filePath = do
  fileContentResult <- Exception.try (TextIO.readFile filePath)
  case fileContentResult of
    Left ioError -> do
      let err = ioError :: Exception.IOException
      putStrLn ("File error: Could not read file '" ++ filePath ++ "': " ++ show err)
      pure Nothing

    Right content ->
      case parseProgram content of
        Left parseError -> do
          TextIO.putStrLn (renderParseError parseError)
          pure Nothing

        Right statements ->
          runStatements initialContext statements

runStatements :: Context -> [Statement] -> IO (Maybe Context)
runStatements currentContext [] = pure (Just currentContext)
runStatements currentContext (statement : remaining) =
  case statement of
    Definition name declaredType bodyTerm ->
      case checkDefinition currentContext name declaredType bodyTerm of
        Left typeError -> do
          TextIO.putStrLn
            ( "Type Error in definition '"
                <> prettyIdentifier name
                <> "':\n  "
                <> renderTypeError typeError
            )
          pure Nothing

        Right updatedContext -> do
          TextIO.putStrLn
            ( "Verified '"
                <> prettyIdentifier name
                <> "' : "
                <> prettyExpression declaredType
            )
          runStatements updatedContext remaining

    Evaluation expression ->
      case synthesize currentContext expression of
        Left typeError -> do
          TextIO.putStrLn ("Type Error in expression: " <> renderTypeError typeError)
          pure Nothing

        Right inferredType -> do
          let values = contextValues currentContext
          TextIO.putStrLn ("Evaluated:  " <> prettyExpression (normalize values expression))
          TextIO.putStrLn ("Type:       " <> prettyExpression (normalize values inferredType))
          runStatements currentContext remaining
