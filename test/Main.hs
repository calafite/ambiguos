{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import AST (Expression (..), Literal (..), Pattern (..), Identifier (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Lexer (PosToken (..), Token (..), tokenize)
import Parser (parseExpression, parseProgram)
import Pretty (prettyExpression)
import Evaluation (Value (..), emptyEnvironment, evaluate, areDefinitionallyEqual)
import System.Exit (exitFailure)

assert :: Bool -> String -> IO ()
assert True _ = pure ()
assert False msg = putStrLn ("FAIL: " ++ msg) >> exitFailure

parseOrDie :: Text -> IO Expression
parseOrDie source = case parseExpression source of
    Right e -> pure e
    Left err -> putStrLn ("FAIL: parse error in " ++ Text.unpack source ++ ": " ++ show err) >> exitFailure

main :: IO ()
main = do
    toks <- either (const exitFailure) pure (tokenize "x :: Int; xs@(x : rest)")
    assert (TokenDoubleColon `elem` map tokenValue toks) ":: lexes as a distinct token"
    assert (TokenColon `elem` map tokenValue toks) ": lexes as a distinct token"
    annotated <- parseOrDie "x :: Int"
    assert (prettyExpression annotated == "x :: Int") "annotations use ::"
    consExpr <- parseOrDie "'h' : \"ello\""
    assert (evaluate emptyEnvironment consExpr == VLit (LitString "hello")) "cons fuses into packed Text"
    listExpr <- parseOrDie "['a', 'b', 'c']"
    stringExpr <- parseOrDie "\"abc\""
    assert (areDefinitionallyEqual emptyEnvironment listExpr stringExpr) "character lists equal packed strings"
    aliases <- either (\err -> putStrLn ("FAIL: alias parse: " ++ show err) >> exitFailure) pure
        (parseProgram "type String = [Char]")
    assert (length aliases == 1) "type synonym syntax parses"
    conditional <- parseOrDie "if True then 1 else 2"
    case unwrap conditional of
        Case _ _ branches -> assert (length branches == 2) "if desugars to two branches"
        _ -> assert False "if desugars to Case"
    program <- either (\err -> putStrLn ("FAIL: program parse: " ++ show err) >> exitFailure) pure
        (parseProgram "data Bool = False | True\n\nidentity :: a -> a\nidentity x = x")
    assert (length program == 2) "ordinary data and function declarations parse"
    let pat = PatAs (Identifier "xs") (PatCon (Identifier ":") [PatVar (Identifier "x"), PatWild])
    assert (pat == PatAs (Identifier "xs") (PatCon (Identifier ":") [PatVar (Identifier "x"), PatWild])) "pattern AST supports as/cons"
    clean <- readFile "chuddy.amb"
    case parseProgram (Text.pack clean) of
        Left err -> putStrLn ("FAIL: clean chuddy syntax parses: " ++ show err) >> exitFailure
        Right _ -> pure ()
    prelude <- readFile "prelude.amb"
    case parseProgram "identity :: a -> a\nidentity x = x" of
        Left err -> putStrLn ("FAIL: identity parses: " ++ show err) >> exitFailure
        Right _ -> pure ()
    case parseProgram (Text.pack prelude) of
        Left err -> putStrLn ("FAIL: prelude parses: " ++ show err) >> exitFailure
        Right _ -> pure ()
    putStrLn "ok"

unwrap :: Expression -> Expression
unwrap (Located _ e) = unwrap e
unwrap e = e
