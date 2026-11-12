{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import AST (Identifier (..), Statement (..))
import qualified Control.Exception as Exception
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Evaluation (normalize)
import Parser (parseProgram, parseStatement, renderParseErrorWithSource)
import Pretty (prettyExpression, prettyIdentifier)
import System.Console.Haskeline (
    InputT,
    Settings (..),
    getInputLine,
    outputStr,
    outputStrLn,
    runInputT,
    simpleCompletion,
 )
import qualified System.Console.Haskeline as Haskeline
import qualified System.Directory as Directory
import System.Environment (getArgs)
import qualified System.Process as Process
import TypeChecker (
    Context (..),
    checkDataDeclaration,
    checkDefinition,
    emptyContext,
    renderGoals,
    renderTypeError,
    synthesize,
 )

bold, dim, green, cyan, magenta, red, yellow :: Text -> Text
bold t = "\ESC[1m" <> t <> "\ESC[0m"
dim t = "\ESC[2m" <> t <> "\ESC[0m"
green t = "\ESC[32m" <> t <> "\ESC[0m"
cyan t = "\ESC[36m" <> t <> "\ESC[0m"
magenta t = "\ESC[35m" <> t <> "\ESC[0m"
red t = "\ESC[31m" <> t <> "\ESC[0m"
yellow t = "\ESC[33m" <> t <> "\ESC[0m"

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> do
            printWelcomeBanner
            runReplWithHaskeline emptyContext
        [filePath] -> do
            TextIO.putStrLn (dim "●" <> " Verifying " <> bold (Text.pack filePath) <> dim "...")
            result <- loadFile emptyContext filePath
            case result of
                Just contextWithFile -> do
                    TextIO.putStrLn ("\n" <> bold (magenta "Ambiguos") <> dim " interactive REPL ready.")
                    TextIO.putStrLn (dim "Type expressions or 'quit' to exit.\n")
                    runReplWithHaskeline contextWithFile
                Nothing ->
                    TextIO.putStrLn (red "✗ " <> "Verification aborted.")
        _ ->
            TextIO.putStrLn (dim "Usage: " <> bold "ambiguos [file.amb]")

printWelcomeBanner :: IO ()
printWelcomeBanner = do
    TextIO.putStrLn ("\n" <> bold (magenta "Ambiguos") <> " " <> dim "v0.1.0" <> " — " <> dim "Formal Verification System")
    TextIO.putStrLn (dim "Calculus of Constructions with Martin-Löf Identity")
    TextIO.putStrLn (dim "Commands: def <name> = <term> | data <name> ... | :load <file> | :paste | :!<command> | quit\n")

runReplWithHaskeline :: Context -> IO ()
runReplWithHaskeline initialContext = do
    contextRef <- newIORef initialContext
    homeDir <- Exception.catch Directory.getHomeDirectory (\(_ :: Exception.IOException) -> pure ".")
    let historyPath = homeDir ++ "/.ambiguos_history"
        settings =
            Settings
                { complete = replCompletion contextRef
                , historyFile = Just historyPath
                , autoAddHistory = True
                }
    runInputT settings (replLoop contextRef)

replCompletion :: IORef Context -> Haskeline.CompletionFunc IO
replCompletion contextRef = Haskeline.completeWord Nothing " \t(){}[];:" $ \word -> do
    ctx <- liftIO (readIORef contextRef)
    let userDefs = map unIdentifier (Map.keys (contextTypes ctx) ++ Map.keys (contextData ctx))
        builtins =
            [ "def"
            , "data"
            , "where"
            , "case"
            , "of"
            , "let"
            , "in"
            , "Type"
            , "Nat"
            , "zero"
            , "successor"
            , "natRec"
            , "Id"
            , "refl"
            , "J"
            , "Void"
            , "abort"
            , ":load"
            , ":l"
            , ":paste"
            , ":!"
            , "quit"
            ]
        allCandidates = map Text.unpack (userDefs ++ builtins)
    pure [simpleCompletion c | c <- allCandidates, List.isPrefixOf word c]

isInputComplete :: Text -> Bool
isInputComplete txt =
    let chars = Text.unpack txt
        (delims, commentDepth) = checkDelimiters chars [] (0 :: Int)
        stripped = Text.stripEnd txt
        dangling = any (`Text.isSuffixOf` stripped) ["=", "\\", "->", "|", "where", "let", "in", "of", ","]
     in null delims && commentDepth == 0 && not dangling
  where
    checkDelimiters [] stack depth = (stack, depth)
    checkDelimiters ('-' : '-' : rest) stack depth
        | depth == 0 = checkDelimiters (dropWhile (/= '\n') rest) stack depth
    checkDelimiters ('{' : '-' : rest) stack depth =
        checkDelimiters rest stack (depth + 1)
    checkDelimiters ('-' : '}' : rest) stack depth =
        checkDelimiters rest stack (max 0 (depth - 1))
    checkDelimiters (c : rest) stack depth
        | depth > 0 = checkDelimiters rest stack depth
        | c == '(' = checkDelimiters rest (')' : stack) depth
        | c == '[' = checkDelimiters rest (']' : stack) depth
        | c == '{' = checkDelimiters rest ('}' : stack) depth
        | c `elem` [')', ']', '}'] =
            case stack of
                (top : xs) | top == c -> checkDelimiters rest xs depth
                _ -> checkDelimiters rest stack depth
        | otherwise = checkDelimiters rest stack depth

readMultiLine :: Text -> InputT IO (Maybe Text)
readMultiLine current
    | isInputComplete current = pure (Just current)
    | otherwise = do
        mNext <- getInputLine "\ESC[2m  ›\ESC[0m "
        case mNext of
            Nothing -> pure (Just current)
            Just nextLine -> readMultiLine (current <> "\n" <> Text.pack nextLine)

readPasteMode :: [Text] -> InputT IO Text
readPasteMode acc = do
    mLine <- getInputLine "\ESC[2mpaste›\ESC[0m "
    case mLine of
        Nothing -> pure (Text.unlines (reverse acc))
        Just line
            | all isSpace line -> pure (Text.unlines (reverse acc))
            | otherwise -> readPasteMode (Text.pack line : acc)

replLoop :: IORef Context -> InputT IO ()
replLoop contextRef = do
    mLine <- getInputLine "\ESC[1m\ESC[35mλ\ESC[0m \ESC[36m›\ESC[0m "
    case mLine of
        Nothing -> outputStrLn "\nTerminating session."
        Just "quit" -> outputStrLn "Terminating session."
        Just rawStr -> do
            let rawInput = Text.pack rawStr
            case () of
                _ | Text.isPrefixOf ":!" rawInput -> do
                    let cmd = Text.unpack (Text.strip (Text.drop 2 rawInput))
                    liftIO (runShellCommand cmd)
                    replLoop contextRef
                _ | rawInput == ":paste" -> do
                    outputStrLn "// Entering paste mode (empty line or Ctrl-D to finish):"
                    pastedContent <- readPasteMode []
                    processStatement contextRef pastedContent
                    replLoop contextRef
                _ | Text.isPrefixOf ":load " rawInput || Text.isPrefixOf ":l " rawInput -> do
                    let filePath = Text.unpack (Text.strip (Text.dropWhile (/= ' ') rawInput))
                    currentContext <- liftIO (readIORef contextRef)
                    mUpdated <- liftIO (loadFile currentContext filePath)
                    case mUpdated of
                        Just newCtx -> liftIO (writeIORef contextRef newCtx)
                        Nothing -> pure ()
                    replLoop contextRef
                _ -> do
                    mFull <- readMultiLine rawInput
                    case mFull of
                        Just completeInput -> do
                            processStatement contextRef completeInput
                            replLoop contextRef
                        Nothing -> pure ()

processStatement :: IORef Context -> Text -> InputT IO ()
processStatement contextRef input
    | Text.null (Text.strip input) = pure ()
    | otherwise = do
        context <- liftIO (readIORef contextRef)
        case parseStatement input of
            Left parseError ->
                outputStrLn (Text.unpack (red "✗ " <> renderParseErrorWithSource Nothing (Just input) parseError))
            Right (DataDeclaration name params univ constrs) ->
                case checkDataDeclaration context name params univ constrs of
                    Left typeError ->
                        outputStrLn (Text.unpack (red "✗ " <> renderTypeError typeError))
                    Right updatedContext -> do
                        let conNames = Text.intercalate ", " (map (prettyIdentifier . fst) constrs)
                        outputStrLn (Text.unpack (green "✓" <> " Defined data " <> bold (prettyIdentifier name) <> " with: " <> cyan conNames))
                        liftIO (writeIORef contextRef updatedContext)
            Right (Definition name maybeType bodyTerm) ->
                case checkDefinition context name maybeType bodyTerm of
                    Left typeError ->
                        outputStrLn (Text.unpack (red "✗ " <> renderTypeError typeError))
                    Right (updatedContext, finalType, goals) -> do
                        if null goals
                            then outputStrLn (Text.unpack (green "✓" <> " Defined " <> bold (prettyIdentifier name) <> " " <> dim ":" <> " " <> magenta (prettyExpression finalType)))
                            else do
                                outputStrLn (Text.unpack (yellow "⚠" <> " Defined " <> bold (prettyIdentifier name) <> " with " <> bold (Text.pack (show (length goals))) <> " goal(s):"))
                                outputStr (Text.unpack (renderGoals goals))
                        liftIO (writeIORef contextRef updatedContext)
            Right (Evaluation expression) -> do
                case synthesize context expression of
                    Left typeError ->
                        outputStrLn (Text.unpack (red "✗ " <> renderTypeError typeError))
                    Right (elaboratedExpr, inferredType, goals) -> do
                        let values = contextValues context
                        evalResult <-
                            liftIO $
                                Exception.try $
                                    Exception.evaluate
                                        ( normalize values inferredType
                                        , normalize values elaboratedExpr
                                        )
                        case evalResult of
                            Left (ex :: Exception.SomeException) ->
                                outputStrLn (Text.unpack (red "✗ " <> "Evaluation exception: " <> Text.pack (show ex)))
                            Right (normType, normExpr) -> do
                                outputStrLn (Text.unpack ("  " <> dim ":" <> " " <> magenta (prettyExpression normType)))
                                outputStrLn (Text.unpack ("  " <> dim "=" <> " " <> bold (green (prettyExpression normExpr))))
                                if null goals
                                    then pure ()
                                    else do
                                        outputStrLn (Text.unpack (yellow "⚠" <> " Unsolved goal(s):"))
                                        outputStr (Text.unpack (renderGoals goals))

runShellCommand :: String -> IO ()
runShellCommand cmd = do
    cmdResult <- Exception.try (Process.callCommand cmd) :: IO (Either Exception.IOException ())
    case cmdResult of
        Left err -> TextIO.putStrLn (red "✗ " <> "Shell error: " <> Text.pack (show err))
        Right () -> pure ()

loadFile :: Context -> FilePath -> IO (Maybe Context)
loadFile initialContext filePath = do
    fileContentResult <- Exception.try (TextIO.readFile filePath)
    case fileContentResult of
        Left ioException -> do
            let err = ioException :: Exception.IOException
            TextIO.putStrLn (red "✗ " <> "Could not read file '" <> Text.pack filePath <> "': " <> Text.pack (show err))
            pure Nothing
        Right content ->
            case parseProgram content of
                Left parseError -> do
                    TextIO.putStrLn (red "✗ " <> renderParseErrorWithSource (Just filePath) (Just content) parseError)
                    pure Nothing
                Right statements -> do
                    runResult <- runStatements initialContext [] filePath content statements
                    case runResult of
                        Nothing -> pure Nothing
                        Just (updatedContext, loadedNames) -> do
                            if null loadedNames
                                then pure ()
                                else do
                                    let countText = Text.pack (show (length loadedNames))
                                    TextIO.putStrLn (green "✓" <> " Verified " <> bold (Text.pack filePath) <> " " <> dim ("(" <> countText <> " definitions)"))
                                    TextIO.putStr (formatWrappedList 72 loadedNames)
                            pure (Just updatedContext)

statementIdentifier :: Statement -> Identifier
statementIdentifier (Definition name _ _) = name
statementIdentifier (DataDeclaration name _ _ _) = name
statementIdentifier (Evaluation _) = Identifier "<expr>"

statementIdentifiers :: Statement -> [Identifier]
statementIdentifiers (Definition name _ _) = [name]
statementIdentifiers (DataDeclaration name _ _ constrs) = name : map fst constrs
statementIdentifiers (Evaluation _) = []

runStatements :: Context -> [Identifier] -> FilePath -> Text -> [Statement] -> IO (Maybe (Context, [Identifier]))
runStatements currentContext accNames _ _ [] = pure (Just (currentContext, reverse accNames))
runStatements currentContext accNames filePath content (statement : remaining) = do
    let name = statementIdentifier statement
    execResult <- Exception.try $ Exception.evaluate $ case statement of
        DataDeclaration dName params univ constrs ->
            case checkDataDeclaration currentContext dName params univ constrs of
                Left typeError ->
                    Left (red "✗ " <> "Type error in data '" <> bold (prettyIdentifier dName) <> "':\n  " <> renderTypeError typeError)
                Right updatedContext -> Right updatedContext
        Definition defName maybeType bodyTerm ->
            case checkDefinition currentContext defName maybeType bodyTerm of
                Left typeError ->
                    Left (red "✗ " <> "Type error in definition '" <> bold (prettyIdentifier defName) <> "':\n  " <> renderTypeError typeError)
                Right (updatedContext, _, goals) ->
                    if null goals
                        then Right updatedContext
                        else
                            Left
                                ( red "✗ "
                                    <> "Definition '"
                                    <> bold (prettyIdentifier defName)
                                    <> "' contains "
                                    <> bold (Text.pack (show (length goals)))
                                    <> " unsolved goal(s):\n"
                                    <> renderGoals goals
                                )
        Evaluation expression ->
            case synthesize currentContext expression of
                Left typeError ->
                    Left (red "✗ " <> "Error in expression: " <> renderTypeError typeError)
                Right (elaboratedExpr, inferredType, goals) ->
                    let values = contextValues currentContext
                     in if null goals
                            then Right currentContext
                            else Left (red "✗ " <> "Expression contains unsolved goal(s):\n" <> renderGoals goals)
    case execResult of
        Left (ex :: Exception.SomeException) -> do
            TextIO.putStrLn (red "✗ " <> "Internal runtime exception in '" <> bold (prettyIdentifier name) <> "': " <> Text.pack (show ex))
            pure Nothing
        Right (Left errMsg) -> do
            TextIO.putStrLn errMsg
            pure Nothing
        Right (Right updatedContext) ->
            let newNames = statementIdentifiers statement
             in runStatements updatedContext (reverse newNames ++ accNames) filePath content remaining

formatWrappedList :: Int -> [Identifier] -> Text
formatWrappedList maxColumns idents =
    Text.unlines (map (\line -> "  " <> dim (Text.intercalate ", " line)) (groupWords 0 [] (map prettyIdentifier idents)))
  where
    groupWords _ currentLine [] = [reverse currentLine | not (null currentLine)]
    groupWords currentLen currentLine (w : ws)
        | currentLen + Text.length w + 2 > maxColumns && not (null currentLine) =
            reverse currentLine : groupWords 0 [] (w : ws)
        | otherwise =
            groupWords (currentLen + Text.length w + 2) (w : currentLine) ws
