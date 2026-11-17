{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import AST (Expression (..), Literal (..), Pattern (..), Identifier (..), PrimType (..), Visibility (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Evaluation (Neutral (..), Value (..), areDefinitionallyEqual, emptyEnvironment, evaluate)
import Lexer (PosToken (..), Token (..), tokenize)
import qualified Module
import Parser (parseExpression, parseProgram)
import Pretty (prettyExpression)
import System.Exit (exitFailure)
import TypeChecker (Context (..), checkStatement, lookupContext, synthesize)

assert :: Bool -> String -> IO ()
assert True _ = pure ()
assert False msg = putStrLn ("FAIL: " ++ msg) >> exitFailure

assertType :: Context -> Text -> String -> IO ()
assertType context name expected =
    case lookupContext (Identifier name) context of
        Left err -> putStrLn ("FAIL: missing binding " ++ Text.unpack name ++ ": " ++ show err) >> exitFailure
        Right inferredType ->
            let actual = Text.unpack (prettyExpression inferredType)
             in assert (actual == expected) ("type of " ++ Text.unpack name ++ " was " ++ actual ++ ", expected " ++ expected)

parseOrDie :: Text -> IO Expression
parseOrDie source = case parseExpression source of
    Right e -> pure e
    Left err -> putStrLn ("FAIL: parse error in " ++ Text.unpack source ++ ": " ++ show err) >> exitFailure

loadOrDie :: FilePath -> IO Context
loadOrDie path = do
    result <- Module.loadModule path
    case result of
        Left err -> putStrLn ("FAIL: module load " ++ path ++ ": " ++ show err) >> exitFailure
        Right context -> pure context

evalOrDie :: Context -> Text -> IO Value
evalOrDie context source = do
    expression <- parseOrDie source
    case synthesize context expression of
        Left err -> putStrLn ("FAIL: type error in " ++ Text.unpack source ++ ": " ++ show err) >> exitFailure
        Right (elaborated, _, _) -> pure (evaluate (contextRuntimeEnv context) elaborated)

defineOrDie :: Context -> Text -> IO Context
defineOrDie context source = do
    statements <- either (\err -> putStrLn ("FAIL: definition parse: " ++ show err) >> exitFailure) pure (parseProgram source)
    foldl define (pure context) statements
  where
    define ioContext statement = do
        current <- ioContext
        case checkStatement current statement of
            Left err -> putStrLn ("FAIL: definition typecheck: " ++ show err) >> exitFailure
            Right (updated, _, goals) -> do
                assert (null goals) ("inference left goals for " ++ Text.unpack source)
                pure updated

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
    preludeContext <- loadOrDie "prelude.amb"
    reversed <- evalOrDie preludeContext "reverse \"hello\""
    assert (reversed == VLit (LitString "olleh")) "prelude reverse evaluates"
    lengthValue <- evalOrDie preludeContext "length \"hello\""
    assert (lengthValue == VLit (LitInt 5)) "prelude length evaluates"
    appended <- evalOrDie preludeContext "append \"foo\" \"bar\""
    assert (appended == VLit (LitString "foobar")) "prelude string append evaluates"
    bindingsContext <- loadOrDie "bindings.amb"
    proof <- evalOrDie bindingsContext "additionZeroRight Zero"
    assert (proof == VRefl (VNeutral (NVar (Identifier "Nat"))) (VCon (Identifier "Zero") [])) "dependent proof evaluates"
    chuddyContext <- loadOrDie "chuddy.amb"
    fibonacciValue <- evalOrDie chuddyContext "fibonacci 8"
    assert (fibonacciValue == VLit (LitInt 21)) "partial fibonacci evaluates"
    lastValue <- evalOrDie chuddyContext "lastElement [1, 2, 3]"
    assert (lastValue == VCon (Identifier "Just") [(Implicit, VPrimType PTInt), (Explicit, VLit (LitInt 3))]) "polymorphic list pattern evaluates"
    inferredContext <- defineOrDie preludeContext "ronaldo x = if x then \"cio\" else \"normal\""
    assert (lookupContext (Identifier "ronaldo") inferredContext == Right (Pi Explicit (Identifier "x") (Variable (Identifier "Bool")) (Application Explicit (Variable (Identifier "List")) (PrimType PTChar)))) "boolean function infers its input type"
    ronaldoTrue <- evalOrDie inferredContext "ronaldo True"
    assert (ronaldoTrue == VLit (LitString "cio")) "inferred boolean function evaluates"
    ronaldoFalse <- evalOrDie inferredContext "ronaldo False"
    assert (ronaldoFalse == VLit (LitString "normal")) "inferred boolean function evaluates on False"
    eqContext <- defineOrDie inferredContext "ronaldoEq x = if x == True then \"cio\" else \"normal\""
    assertType eqContext "ronaldoEq" "(x :: Bool) -> List Char"
    ronaldoEqTrue <- evalOrDie eqContext "ronaldoEq True"
    assert (ronaldoEqTrue == VLit (LitString "cio")) "inferred equality function evaluates"
    inferredContext2 <- defineOrDie eqContext "addOne x = x + 1"
    assertType inferredContext2 "addOne" "(x :: Int) -> Int"
    addOneValue <- evalOrDie inferredContext2 "addOne 41"
    assert (addOneValue == VLit (LitInt 42)) "inferred arithmetic function evaluates"
    invalidExpression <- parseOrDie "True + 1"
    case synthesize preludeContext invalidExpression of
        Left _ -> pure ()
        Right _ -> assert False "invalid arithmetic is rejected"
    floatSum <- evalOrDie preludeContext "1.5 + 1"
    assert (floatSum == VLit (LitFloat 2.5)) "mixed int/float arithmetic coerces to float"
    polymorphicContext <- defineOrDie inferredContext2 "myId x = x\nmyApply f x = f x"
    assertType polymorphicContext "myId" "{a :: Type} -> (x :: a) -> a"
    assertType polymorphicContext "myApply" "{a :: Type} -> {b :: Type} -> (f :: a -> b) -> (x :: a) -> b"
    myIdTrue <- evalOrDie polymorphicContext "myId True"
    myIdInt <- evalOrDie polymorphicContext "myId 42"
    assert (myIdTrue == VCon (Identifier "True") []) "generalized identity accepts Bool"
    assert (myIdInt == VLit (LitInt 42)) "generalized identity accepts Int"
    myApplyValue <- evalOrDie polymorphicContext "myApply not True"
    assert (myApplyValue == VCon (Identifier "False") []) "generalized application evaluates"
    holeProgram <- either (\err -> putStrLn ("FAIL: hole parse: " ++ show err) >> exitFailure) pure
        (parseProgram "foo :: Int -> Int\nfoo x = _")
    case holeProgram of
        [holeStatement] ->
            case checkStatement preludeContext holeStatement of
                Left err -> putStrLn ("FAIL: hole typecheck: " ++ show err) >> exitFailure
                Right (holeContext, _, goals) -> do
                    assert (not (null goals)) "explicit holes report unsolved goals"
                    assert (lookupContext (Identifier "foo") holeContext == Right (Pi Explicit (Identifier "_") (PrimType PTInt) (PrimType PTInt))) "explicit holes keep the declared type"
        _ -> assert False "hole program has a single definition"
    putStrLn "ok"

unwrap :: Expression -> Expression
unwrap (Located _ e) = unwrap e
unwrap e = e
