{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text.IO as TextIO
import Evaluation (normalize)
import Parser (parseExpression)
import Pretty (prettyExpression)
import System.IO (hFlush, stdout)
import Text.Megaparsec (errorBundlePretty)
import TypeChecker (emptyContext, renderTypeError, synthesize)

main :: IO ()
main = do
  putStrLn "Ambiguos Formal Verification System"
  putStrLn "Enter an expression or 'quit' to terminate."
  replLoop

replLoop :: IO ()
replLoop = do
  putStr "> "
  hFlush stdout
  rawInput <- TextIO.getLine
  if rawInput == "quit"
    then putStrLn "Terminating session."
    else do
      case parseExpression rawInput of
        Left parseError ->
          putStrLn (errorBundlePretty parseError)
        Right abstractSyntaxTree ->
          case synthesize emptyContext abstractSyntaxTree of
            Left typeError ->
              TextIO.putStrLn ("Type Error: " <> renderTypeError typeError)
            Right inferredType -> do
              TextIO.putStrLn ("Type:       " <> prettyExpression (normalize inferredType))
              TextIO.putStrLn ("Normalized: " <> prettyExpression (normalize abstractSyntaxTree))
      replLoop
