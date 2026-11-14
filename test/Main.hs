{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import AST (CaseBranch (..), Expression (..), Identifier (..), Statement (..), Visibility (..))
import Data.Either (isLeft)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Data.Maybe (isJust)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Diagnostics (SourcePos (..), SourceSpan (..), spanStart)
import Evaluation (areDefinitionallyEqual)
import Parser (ParseError (..), defaultFixityEnv, parseExpression, parseProgram, renderParseErrorWithSource)
import Pretty (PrettyConfig (..), prettyExpression, prettyExpressionWith)
import System.Exit (exitFailure, exitSuccess)
import TypeChecker (
    Context, Goal (..), TypeDiagnostic (..),
    check, checkDataDeclaration, checkDefinition, emptyContext, renderTypeDiagnostic,
    synthesize,
  )

--------------------------------------------------------------
-- Test harness
--------------------------------------------------------------

renderParseError :: ParseError -> Text
renderParseError = renderParseErrorWithSource Nothing Nothing

assert :: IORef Int -> Bool -> String -> IO ()
assert ref True _ = pure ()
assert ref False msg = modifyIORef' ref (+1) >> putStrLn ("FAIL: " ++ msg)

assertEqual :: (Eq a, Show a) => IORef Int -> a -> a -> String -> IO ()
assertEqual ref actual expected msg =
    if actual == expected
        then pure ()
        else modifyIORef' ref (+1) >>
             putStrLn ("FAIL: " ++ msg ++ " (expected " ++ show expected ++ ", got " ++ show actual ++ ")")

assertRight :: IORef Int -> Either TypeDiagnostic a -> String -> IO (Maybe a)
assertRight ref (Right x) _ = pure (Just x)
assertRight ref (Left e) msg =
    modifyIORef' ref (+1) >>
    putStrLn ("FAIL: " ++ msg ++ " (got Left: " ++ Text.unpack (renderTypeDiagnostic Nothing Nothing e) ++ ")") >>
    pure Nothing

parseOk :: IORef Int -> Text -> IO Expression
parseOk ref input =
    case parseExpression input of
        Right e -> pure e
        Left e -> modifyIORef' ref (+1) >>
                  putStrLn ("FAIL: parse should succeed: " ++ Text.unpack (renderParseError e)) >>
                  pure Zero

parseMulti :: IORef Int -> Text -> IO Expression
parseMulti ref input =
    case parseExpression input of
        Right e -> pure e
        Left e -> modifyIORef' ref (+1) >>
                  putStrLn ("FAIL: unexpected parse error: " ++ Text.unpack (renderParseError e)) >>
                  pure Zero

assertSpanLine :: IORef Int -> TypeDiagnostic -> Int -> IO ()
assertSpanLine ref diag expectedLine =
    case diagSpan diag of
        Just sp ->
            assert ref (posLine (spanStart sp) == expectedLine)
                ("span line " ++ show (posLine (spanStart sp)) ++ " == " ++ show expectedLine)
        Nothing ->
            modifyIORef' ref (+1) >>
            putStrLn ("FAIL: expected span at line " ++ show expectedLine ++ ", got Nothing")

--------------------------------------------------------------
-- Helpers
--------------------------------------------------------------

natLit :: Integer -> Expression
natLit 0 = Zero
natLit n = Application Explicit Succ (natLit (n - 1))

appN :: Expression -> [(Visibility, Expression)] -> Expression
appN = foldl (\acc (vis, arg) -> Application vis acc arg)

bIdent = Identifier "b"
trueC = Identifier "true"
falseC = Identifier "false"

caseBranches1 = [CaseBranch trueC [] (natLit 0), CaseBranch falseC [] (natLit 1)]
caseBranches2 = [CaseBranch trueC [] (natLit 0), CaseBranch falseC [] (natLit 0)]

caseNCase1 = Lambda Explicit bIdent (Just NatType) (Case (Variable bIdent) Nothing caseBranches1)
caseNCase2 = Lambda Explicit bIdent (Just NatType) (Case (Variable bIdent) Nothing caseBranches2)

--------------------------------------------------------------
-- 1. Lexer & Parser
--------------------------------------------------------------

testLexerParser :: IORef Int -> IO ()
testLexerParser ref = do
    nested <- parseOk ref "{- {- inner -} -} 42"
    assertEqual ref (prettyExpression nested) "42" "nested block comment desugars to 42"
    lined <- parseOk ref "42 -- trailing comment"
    assertEqual ref (prettyExpression lined) "42" "line comment desugars to 42"
    num <- parseOk ref "3"
    assertEqual ref (prettyExpression num) "3" "numeric literal 3"
    lst <- parseOk ref "[1, 2]"
    assertEqual ref (prettyExpression lst) "[1, 2]" "list literal [1, 2]"
    case parseExpression "x =" of
        Left (UnexpectedToken _ (SourcePos line col)) ->
            assert ref (line == 1 && col == 3) "parse error '=' at line 1 col 3"
        Left e -> modifyIORef' ref (+1) >>
                  putStrLn ("FAIL: expected UnexpectedToken, got " ++ show e)
        Right _ -> modifyIORef' ref (+1) >>
                   putStrLn "FAIL: 'x =' should be a parse error"

--------------------------------------------------------------
-- 2. Pretty-Printer regressions
--------------------------------------------------------------

testPretty :: IORef Int -> IO ()
testPretty ref = do
    xy <- parseOk ref "x + y"
    assertEqual ref (prettyExpression xy) "x + y" "x + y"
    fg <- parseOk ref "f x + g y"
    assertEqual ref (prettyExpression fg) "f x + g y" "f x + g y"
    ab <- parseOk ref "a + (b + c)"
    assertEqual ref (prettyExpression ab) "a + (b + c)" "a + (b + c) keeps parens"
    abc <- parseOk ref "(a + b) + c"
    assertEqual ref (prettyExpression abc) "a + b + c" "(a + b) + c is left assoc"
    hidExpr <- parseOk ref "identity {Nat} x"
    let hid = prettyExpressionWith (PrettyConfig False defaultFixityEnv) hidExpr
    assertEqual ref hid "identity x" "PrettyConfig False hides implicit {Nat}"
    let shown = prettyExpression hidExpr
    assertEqual ref shown "identity {Nat} x" "default shows implicit {Nat}"

--------------------------------------------------------------
-- 3. Evaluation / NbE regressions
--------------------------------------------------------------

testEvaluation :: IORef Int -> IO ()
testEvaluation ref = do
    let neq = areDefinitionallyEqual Map.empty caseNCase1 caseNCase2
    assert ref (not neq) "NCase with different bodies is not definitionally equal"
    let eq = areDefinitionallyEqual Map.empty caseNCase1 caseNCase1
    assert ref eq "NCase identical is definitionally equal"
    let caseAlpha = Lambda Explicit (Identifier "b2") (Just NatType) (Case (Variable (Identifier "b2")) Nothing caseBranches1)
    let eqAlpha = areDefinitionallyEqual Map.empty caseNCase1 caseAlpha
    assert ref eqAlpha "alpha-equivalent NCase is definitionally equal"
    let beta1 =
            Application Explicit
                (Lambda Explicit (Identifier "x") Nothing (Variable (Identifier "x")))
                (Variable (Identifier "y"))
    let betaEq = areDefinitionallyEqual Map.empty beta1 (Variable (Identifier "y"))
    assert ref betaEq "beta reduction (\\x -> x) y == y"
    let eta1 =
            Lambda Explicit
                (Identifier "x")
                Nothing
                (Application Explicit (Variable (Identifier "f")) (Variable (Identifier "x")))
    let etaEq = areDefinitionallyEqual Map.empty eta1 (Variable (Identifier "f"))
    assert ref etaEq "eta equality (\\x -> f x) == f"
    let p = Universe (-1)
        z = Zero
        k = Identifier "k"
        rec = Identifier "rec"
        step = Lambda Explicit k Nothing (Lambda Explicit rec Nothing (Application Explicit Succ (Variable rec)))
        natrecZ = appN NatRec [(Explicit, p), (Explicit, z), (Explicit, step), (Explicit, Zero)]
    let natrecZEq = areDefinitionallyEqual Map.empty natrecZ z
    assert ref natrecZEq "natRec P z s zero == z"
    let natrecS = appN NatRec [(Explicit, p), (Explicit, z), (Explicit, step), (Explicit, Application Explicit Succ Zero)]
    let natrecSRhs = appN step [(Explicit, Zero), (Explicit, natrecZ)]
    let natrecSEq = areDefinitionallyEqual Map.empty natrecS natrecSRhs
    assert ref natrecSEq "natRec P z s (succ zero) == step zero (natRec P z s zero)"

--------------------------------------------------------------
-- 4. TypeChecker positive tests
--------------------------------------------------------------

verifyStmts :: Context -> [Statement] -> IO (Context, Int, Int)
verifyStmts ctx [] = pure (ctx, 0, 0)
verifyStmts ctx (s : ss) =
    case s of
        Definition name mty body ->
            case checkDefinition ctx name mty body of
                Left _ -> do (ctx', e, g) <- verifyStmts ctx ss; pure (ctx', e + 1, g)
                Right (ctx', _, goals) -> do (ctx'', e, g) <- verifyStmts ctx' ss; pure (ctx'', e, g + length goals)
        DataDeclaration name params univ constrs ->
            case checkDataDeclaration ctx name params univ constrs of
                Left _ -> do (ctx', e, g) <- verifyStmts ctx ss; pure (ctx', e + 1, g)
                Right ctx' -> do (ctx'', e, g) <- verifyStmts ctx' ss; pure (ctx'', e, g)
        Evaluation expr ->
            case synthesize ctx expr of
                Left _ -> do (ctx', e, g) <- verifyStmts ctx ss; pure (ctx', e + 1, g)
                Right (_, _, goals) -> do (ctx', e, g) <- verifyStmts ctx ss; pure (ctx', e, g + length goals)

readProgram :: FilePath -> IO [Statement]
readProgram fp = do
    content <- TextIO.readFile fp
    case parseProgram content of
        Right stmts -> pure stmts
        Left e -> error ("Failed to parse " ++ fp ++ ": " ++ Text.unpack (renderParseError e))

testTypeCheckerPositive :: IORef Int -> IO ()
testTypeCheckerPositive ref = do
    prelude <- readProgram "prelude.amb"
    (ctxP, errsP, goalsP) <- verifyStmts emptyContext prelude
    assert ref (errsP == 0) ("prelude.amb: zero errors (got " ++ show errsP ++ ")")
    assert ref (goalsP == 0) ("prelude.amb: zero goals (got " ++ show goalsP ++ ")")
    bindings <- readProgram "bindings.amb"
    (ctxB, errsB, goalsB) <- verifyStmts ctxP bindings
    assert ref (errsB == 0) ("bindings.amb on prelude: zero errors (got " ++ show errsB ++ ")")
    assert ref (goalsB == 0) ("bindings.amb on prelude: zero goals (got " ++ show goalsB ++ ")")
    case check emptyContext (Hole Nothing) NatType of
        Left _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: hole check should typecheck"
        Right (_, goals) -> do
            assert ref (length goals == 1) "checked hole creates exactly one goal"
            case goals of
                [g] -> assert ref (prettyExpression (goalExpected g) == "Nat") "checked hole goal expected type is Nat"
                _ -> pure ()
    case synthesize emptyContext (Hole Nothing) of
        Right (_, _, goals) -> assert ref (length goals >= 1) "synthesized hole creates at least one goal"
        Left _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: synthesized hole should not error"

--------------------------------------------------------------
-- 5. TypeChecker negative tests
--------------------------------------------------------------

testTypeCheckerNegative :: IORef Int -> IO ()
testTypeCheckerNegative ref = do
    unboundExpr <- parseMulti ref "\nx"
    case synthesize emptyContext unboundExpr of
        Left diag -> do
            assert ref (isJust (diagSpan diag)) "unbound variable has a span"
            assertSpanLine ref diag 2
        Right _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: unbound variable should error"
    -- Type mismatch: checking Succ against Nat (Succ : Nat -> Nat)
    succExpr <- parseMulti ref "\nSucc"
    case check emptyContext succExpr NatType of
        Left diag -> do
            assert ref (isJust (diagSpan diag)) "type mismatch has a span"
            assertSpanLine ref diag 2
        Right _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: type mismatch should error"
    appExpr <- parseMulti ref "\nZero Zero"
    case synthesize emptyContext appExpr of
        Left diag -> do
            assert ref (isJust (diagSpan diag)) "expected function type has a span"
            assertSpanLine ref diag 2
        Right _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: expected function type should error"
    caseExpr <- parseMulti ref "\ncase true of { }"
    case synthesize emptyContext caseExpr of
        Left _ -> pure ()
        Right _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: non-exhaustive case should error"
    conExpr <- parseMulti ref "\ncase zero of { foo -> zero }"
    case synthesize emptyContext conExpr of
        Left _ -> pure ()
        Right _ -> modifyIORef' ref (+1) >> putStrLn "FAIL: unknown constructor should error"

--------------------------------------------------------------
-- main
--------------------------------------------------------------

main :: IO ()
main = do
    failed <- newIORef (0 :: Int)
    testLexerParser failed
    testPretty failed
    testEvaluation failed
    testTypeCheckerPositive failed
    testTypeCheckerNegative failed
    n <- readIORef failed
    if n == 0
        then putStrLn "All tests passed" >> exitSuccess
        else putStrLn (show n ++ " test(s) failed") >> exitFailure
