{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import AST (Statement (..))
import qualified Data.Text.IO as TextIO
import Evaluation (normalize)
import Parser (parseStatement)
import Pretty (prettyExpression, prettyIdentifier)
import System.IO (hFlush, stdout)
import Text.Megaparsec (errorBundlePretty)
import TypeChecker
  ( Context (..)
  , checkDefinition
  , emptyContext
  , renderTypeError
  , synthesize
  )

main :: IO ()
main = do
  putStrLn "Ambiguos Formal Verification System"
  putStrLn "Commands: def <name> : <Type> = <term> | <expr> | quit"
  replLoop emptyContext

replLoop :: Context -> IO ()
replLoop context = do
  putStr "> "
  hFlush stdout
  rawInput <- TextIO.getLine
  if rawInput == "quit"
    then putStrLn "Terminating session."
    else do
      case parseStatement rawInput of
        Left parseError -> do
          putStrLn (errorBundlePretty parseError)
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
