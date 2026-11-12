{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import AST (Identifier, Statement (..))
import qualified Control.Exception as Exception
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Evaluation (normalize)
import Parser (parseProgram, parseStatement, renderParseError)
import Pretty (prettyExpression, prettyIdentifier)
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
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
            replLoop emptyContext
        [filePath] -> do
            TextIO.putStrLn (dim "●" <> " Verifying " <> bold (Text.pack filePath) <> dim "...")
            result <- loadFile emptyContext filePath
            case result of
                Just contextWithFile -> do
                    TextIO.putStrLn ("\n" <> bold (magenta "Ambiguos") <> dim " interactive REPL ready.")
                    TextIO.putStrLn (dim "Type expressions or 'quit' to exit.\n")
                    replLoop contextWithFile
                Nothing ->
                    TextIO.putStrLn (red "✗ " <> "Verification aborted.")
        _ ->
            TextIO.putStrLn (dim "Usage: " <> bold "ambiguos [file.amb]")

printWelcomeBanner :: IO ()
printWelcomeBanner = do
    TextIO.putStrLn ("\n" <> bold (magenta "Ambiguos") <> " " <> dim "v0.1.0" <> " — " <> dim "Formal Verification System")
    TextIO.putStrLn (dim "Calculus of Constructions with Martin-Löf Identity")
    TextIO.putStrLn (dim "Commands: def <name> = <term> | data <name> ... | :load <file> | :!<command> | quit\n")

replLoop :: Context -> IO ()
replLoop context = do
    TextIO.putStr (bold (magenta "λ") <> " " <> cyan "›" <> " ")
    hFlush stdout
    rawInput <- TextIO.getLine
    case rawInput of
        "quit" -> TextIO.putStrLn (dim "Terminating session.")
        _
            | Text.isPrefixOf ":!" rawInput -> do
                let shellCommand = Text.unpack (Text.strip (Text.drop 2 rawInput))
                runShellCommand shellCommand
                replLoop context
            | Text.isPrefixOf ":load " rawInput || Text.isPrefixOf ":l " rawInput -> do
                let filePath = Text.unpack (Text.strip (Text.dropWhile (/= ' ') rawInput))
                maybeUpdatedContext <- loadFile context filePath
                case maybeUpdatedContext of
                    Just newContext -> replLoop newContext
                    Nothing -> replLoop context
            | otherwise -> do
                case parseStatement rawInput of
                    Left parseError -> do
                        TextIO.putStrLn (red "✗ " <> renderParseError parseError)
                        replLoop context
                    Right (DataDeclaration name params univ constrs) ->
                        case checkDataDeclaration context name params univ constrs of
                            Left typeError -> do
                                TextIO.putStrLn (red "✗ " <> renderTypeError typeError)
                                replLoop context
                            Right updatedContext -> do
                                let conNames = Text.intercalate ", " (map (prettyIdentifier . fst) constrs)
                                TextIO.putStrLn (green "✓" <> " Defined data " <> bold (prettyIdentifier name) <> " with: " <> cyan conNames)
                                replLoop updatedContext
                    Right (Definition name maybeType bodyTerm) ->
                        case checkDefinition context name maybeType bodyTerm of
                            Left typeError -> do
                                TextIO.putStrLn (red "✗ " <> renderTypeError typeError)
                                replLoop context
                            Right (updatedContext, finalType, goals) -> do
                                if null goals
                                    then
                                        TextIO.putStrLn
                                            ( green "✓"
                                                <> " Defined "
                                                <> bold (prettyIdentifier name)
                                                <> " "
                                                <> dim ":"
                                                <> " "
                                                <> magenta (prettyExpression finalType)
                                            )
                                    else do
                                        TextIO.putStrLn
                                            ( yellow "⚠"
                                                <> " Defined "
                                                <> bold (prettyIdentifier name)
                                                <> " with "
                                                <> bold (Text.pack (show (length goals)))
                                                <> " goal(s):"
                                            )
                                        TextIO.putStr (renderGoals goals)
                                replLoop updatedContext
                    Right (Evaluation expression) -> do
                        case synthesize context expression of
                            Left typeError ->
                                TextIO.putStrLn (red "✗ " <> renderTypeError typeError)
                            Right (elaboratedExpr, inferredType, goals) -> do
                                let values = contextValues context
                                TextIO.putStrLn ("  " <> dim ":" <> " " <> magenta (prettyExpression (normalize values inferredType)))
                                TextIO.putStrLn ("  " <> dim "=" <> " " <> bold (green (prettyExpression (normalize values elaboratedExpr))))
                                if null goals
                                    then pure ()
                                    else do
                                        TextIO.putStrLn (yellow "⚠" <> " Unsolved goal(s):")
                                        TextIO.putStr (renderGoals goals)
                        replLoop context

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
                    TextIO.putStrLn (red "✗ " <> renderParseError parseError)
                    pure Nothing
                Right statements -> do
                    runResult <- runStatements initialContext [] statements
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

runStatements :: Context -> [Identifier] -> [Statement] -> IO (Maybe (Context, [Identifier]))
runStatements currentContext accNames [] = pure (Just (currentContext, reverse accNames))
runStatements currentContext accNames (statement : remaining) =
    case statement of
        DataDeclaration name params univ constrs ->
            case checkDataDeclaration currentContext name params univ constrs of
                Left typeError -> do
                    TextIO.putStrLn
                        ( red "✗ "
                            <> "Error in data '"
                            <> bold (prettyIdentifier name)
                            <> "':\n  "
                            <> renderTypeError typeError
                        )
                    pure Nothing
                Right updatedContext ->
                    runStatements updatedContext (name : accNames) remaining
        Definition name maybeType bodyTerm ->
            case checkDefinition currentContext name maybeType bodyTerm of
                Left typeError -> do
                    TextIO.putStrLn
                        ( red "✗ "
                            <> "Error in definition '"
                            <> bold (prettyIdentifier name)
                            <> "':\n  "
                            <> renderTypeError typeError
                        )
                    pure Nothing
                Right (updatedContext, _, goals) ->
                    if null goals
                        then runStatements updatedContext (name : accNames) remaining
                        else do
                            TextIO.putStrLn
                                ( red "✗ "
                                    <> "Definition '"
                                    <> bold (prettyIdentifier name)
                                    <> "' contains unsolved goal(s):\n"
                                    <> renderGoals goals
                                )
                            pure Nothing
        Evaluation expression ->
            case synthesize currentContext expression of
                Left typeError -> do
                    TextIO.putStrLn (red "✗ " <> "Error in expression: " <> renderTypeError typeError)
                    pure Nothing
                Right (elaboratedExpr, inferredType, goals) -> do
                    let values = contextValues currentContext
                    TextIO.putStrLn ("  " <> dim ":" <> " " <> magenta (prettyExpression (normalize values inferredType)))
                    TextIO.putStrLn ("  " <> dim "=" <> " " <> bold (green (prettyExpression (normalize values elaboratedExpr))))
                    if null goals
                        then pure ()
                        else do
                            TextIO.putStrLn (yellow "⚠" <> " Unsolved goal(s):")
                            TextIO.putStr (renderGoals goals)
                    runStatements currentContext accNames remaining

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
