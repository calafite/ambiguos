{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import AST (Fixity (..), Identifier (..), Statement (..), Visibility (..))
import qualified Control.Exception as Exception
import Control.Monad.IO.Class (liftIO)
import Control.Monad (unless)
import Data.Char (isSpace)
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef')
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Evaluation (normalize)
import Parser (defaultFixityEnv, parseExpression, parseProgramWith, parseStatement, renderParseErrorWithSource)
import Pretty (
    PrettyConfig (..),
    prettyExpression,
    prettyExpressionWith,
    prettyIdentifier
  )
import System.Console.Haskeline (
    InputT,
    Settings (..),
    getInputLine,
    outputStr,
    outputStrLn,
    runInputT,
    simpleCompletion
  )
import qualified System.Console.Haskeline as Haskeline
import qualified System.Directory as Directory
import System.Environment (getArgs)
import qualified System.Process as Process
import TypeChecker (
    Context (..),
    DataInfo (..),
    Goal (..),
    checkDataDeclaration,
    checkDefinition,
    emptyContext,
    lookupContext,
    renderGoals,
    renderTypeDiagnostic,
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

data ReplState = ReplState
    { replContext       :: !Context
    , replLastFile      :: !(Maybe FilePath)
    , replLastGoals     :: ![Goal]
    , replPrettyConfig  :: !PrettyConfig
    }

emptyReplState :: ReplState
emptyReplState = ReplState emptyContext Nothing [] (PrettyConfig True defaultFixityEnv)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> do
            printWelcomeBanner
            runReplWithHaskeline emptyReplState
        [filePath] -> do
            TextIO.putStrLn (dim "●" <> " Verifying " <> bold (Text.pack filePath) <> dim "...")
            result <- loadFileFrom emptyContext filePath
            case result of
                Just contextWithFile -> do
                    TextIO.putStrLn ("\n" <> bold (magenta "Ambiguos") <> dim " interactive REPL ready.")
                    TextIO.putStrLn (dim "Type expressions or 'quit' to exit.\n")
                    runReplWithHaskeline (ReplState contextWithFile (Just filePath) [] (PrettyConfig True defaultFixityEnv))
                Nothing ->
                    TextIO.putStrLn (red "✗ " <> "Verification aborted.")
        _ ->
            TextIO.putStrLn (dim "Usage: " <> bold "ambiguos [file.amb]")

printWelcomeBanner :: IO ()
printWelcomeBanner = do
    TextIO.putStrLn ("\n" <> bold (magenta "Ambiguos") <> " " <> dim "v0.1.0" <> " — " <> dim "Formal Verification System")
    TextIO.putStrLn (dim "Calculus of Constructions with Martin-Löf Identity")
    TextIO.putStrLn (dim "Commands: def <name> = <term> | data <name> ... | :load <file> | :add <file> | :reload | :type <expr> | :info <ident> | :browse | :goals | :set +/-implicits | :paste | :!<command> | :help | quit\n")

runReplWithHaskeline :: ReplState -> IO ()
runReplWithHaskeline initialState = do
    contextRef <- newIORef initialState
    homeDir <- Exception.catch Directory.getHomeDirectory (\(_ :: Exception.IOException) -> pure ".")
    let historyPath = homeDir ++ "/.ambiguos_history"
        settings =
            Settings
                { complete = replCompletion contextRef
                , historyFile = Just historyPath
                , autoAddHistory = True
                }
    runInputT settings (replLoop contextRef)

replCompletion :: IORef ReplState -> Haskeline.CompletionFunc IO
replCompletion contextRef = Haskeline.completeWord Nothing " \t(){}[];:" $ \word -> do
    ReplState{replContext = ctx} <- liftIO (readIORef contextRef)
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
            , ":add"
            , ":a"
            , ":reload"
            , ":r"
            , ":type"
            , ":t"
            , ":info"
            , ":i"
            , ":browse"
            , ":env"
            , ":goals"
            , ":set"
            , ":paste"
            , ":!"
            , "quit"
            , ":help"
            , ":?"
            , "infixl"
            , "infixr"
            , "infix"
            ]
        allCandidates = map Text.unpack (userDefs ++ builtins)
    pure [simpleCompletion c | c <- allCandidates, List.isPrefixOf word c]

-- | Remove line (`-- ...`) and block (`{- ... -}`) comments so that a trailing
-- dangling operator inside a comment is not mistaken for an incomplete input.
cleanSource :: Text -> Text
cleanSource = Text.pack . go (0 :: Int) . Text.unpack
  where
    go :: Int -> String -> String
    go _ [] = ""
    go depth ('{':'-':rest) = go (depth + 1) (drop 2 rest)
    go depth ('-':'}':rest) = go (max 0 (depth - 1)) (drop 2 rest)
    go 0 ('-':'-':rest) = go 0 (dropWhile (/= '\n') rest)
    go depth (_ : rest) | depth > 0 = go depth rest
    go depth (c : rest) = c : go depth rest

isInputComplete :: Text -> Bool
isInputComplete txt =
    let (delims, commentDepth) = checkDelimiters (Text.unpack txt) [] (0 :: Int)
        stripped = Text.stripEnd (cleanSource txt)
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

replLoop :: IORef ReplState -> InputT IO ()
replLoop contextRef = do
    mLine <- getInputLine "\ESC[1m\ESC[35mλ\ESC[0m \ESC[36m›\ESC[0m "
    case mLine of
        Nothing -> outputStrLn "\nTerminating session."
        Just "quit" -> outputStrLn "Terminating session."
        Just rawStr -> do
            let rawInput = Text.pack rawStr
                trimmed = Text.strip rawInput
                (cmdWord, cmdArg) = Text.break isSpace trimmed
            case () of
                _ | Text.isPrefixOf ":!" rawInput -> do
                    let cmd = Text.unpack (Text.strip (Text.drop 2 rawInput))
                    liftIO (runShellCommand cmd)
                    replLoop contextRef
                _ | trimmed == ":paste" -> do
                    outputStrLn "// Entering paste mode (empty line or Ctrl-D to finish):"
                    pastedContent <- readPasteMode []
                    processStatement contextRef pastedContent
                    replLoop contextRef
                _ | cmdWord `elem` [":load", ":l"] -> do
                    let filePath = Text.unpack (Text.strip cmdArg)
                    unless (Text.null cmdArg) $ liftIO (cmdLoadFile contextRef filePath True)
                    replLoop contextRef
                _ | cmdWord `elem` [":add", ":a"] -> do
                    let filePath = Text.unpack (Text.strip cmdArg)
                    unless (Text.null cmdArg) $ liftIO (cmdLoadFile contextRef filePath False)
                    replLoop contextRef
                _ | cmdWord `elem` [":reload", ":r"] -> do
                    cmdReload contextRef
                    replLoop contextRef
                _ | cmdWord == ":goals" -> do
                    cmdGoals contextRef
                    replLoop contextRef
                _ | cmdWord == ":set" -> do
                    let rest = Text.strip cmdArg
                    cmdSet contextRef rest
                    replLoop contextRef
                _ | cmdWord `elem` [":help", ":?"] -> do
                    cmdHelp
                    replLoop contextRef
                _ | cmdWord `elem` [":t", ":type"] -> do
                    let exprText = Text.strip cmdArg
                    unless (Text.null cmdArg) $ cmdType contextRef exprText
                    replLoop contextRef
                _ | cmdWord `elem` [":i", ":info"] -> do
                    let identText = Text.strip cmdArg
                    unless (Text.null cmdArg) $ cmdInfo contextRef identText
                    replLoop contextRef
                _ | cmdWord `elem` [":browse", ":env"] -> do
                    cmdBrowse contextRef
                    replLoop contextRef
                _ -> do
                    mFull <- readMultiLine rawInput
                    case mFull of
                        Just completeInput -> do
                            processStatement contextRef completeInput
                            replLoop contextRef
                        Nothing -> pure ()


cmdLoadFile :: IORef ReplState -> FilePath -> Bool -> IO ()
cmdLoadFile contextRef filePath reset = do
    ReplState{replContext = ctx, replPrettyConfig = cfg} <- readIORef contextRef
    let startCtx = if reset then emptyContext else ctx
    mNew <- loadFileFrom startCtx filePath
    case mNew of
        Just newCtx -> writeIORef contextRef (ReplState newCtx (Just filePath) [] cfg)
        Nothing -> pure ()

cmdReload :: IORef ReplState -> InputT IO ()
cmdReload contextRef = do
    mState <- liftIO (readIORef contextRef)
    case replLastFile mState of
        Nothing -> outputStrLn "No file to reload."
        Just fp -> do
            liftIO (cmdLoadFile contextRef fp True)
            liftIO (modifyIORef' contextRef (\s -> s{replLastGoals = []}))
            outputStrLn "Reloaded."

cmdGoals :: IORef ReplState -> InputT IO ()
cmdGoals contextRef = do
    ReplState{replLastGoals = goals} <- liftIO (readIORef contextRef)
    unless (null goals) $ do
        outputStrLn (Text.unpack (yellow "⚠" <> " Unsolved goal(s):"))
        outputStr (Text.unpack (renderGoals goals))

cmdSet :: IORef ReplState -> Text -> InputT IO ()
cmdSet contextRef rest = case rest of
    "+implicits" -> do
        liftIO (modifyIORef' contextRef (\s -> s{replPrettyConfig = PrettyConfig True defaultFixityEnv}))
        outputStrLn "implicits: on"
    "-implicits" -> do
        liftIO (modifyIORef' contextRef (\s -> s{replPrettyConfig = PrettyConfig False defaultFixityEnv}))
        outputStrLn "implicits: off"
    _ -> outputStrLn "Unknown :set option. Use ':set +implicits' or ':set -implicits'."

cmdHelp :: InputT IO ()
cmdHelp = do
    outputStrLn (Text.unpack (bold "Ambiguos REPL commands:"))
    outputStrLn (Text.unpack "  def <name> [: <type>] = <term>   typecheck and bind a global definition")
    outputStrLn (Text.unpack "  <expr>                         infer type and evaluate to normal form")
    outputStrLn (Text.unpack "  :load <file>                   load and verify a file, resetting context (alias: :l)")
    outputStrLn (Text.unpack "  :add <file>                    load and verify a file, layering onto context (alias: :a)")
    outputStrLn (Text.unpack "  :reload | :r                   reload replLastFile from an empty context")
    outputStrLn (Text.unpack "  :type <expr> | :t <expr>       synthesize and print the normalized type of <expr>")
    outputStrLn (Text.unpack "  :info <ident> | :i <ident>     show information about an identifier")
    outputStrLn (Text.unpack "  :browse | :env                 list all data types and symbols in scope")
    outputStrLn (Text.unpack "  :goals                         re-print unsolved goals from the last statement")
    outputStrLn (Text.unpack "  :set +implicits | -implicits   show or hide implicit arguments in output")
    outputStrLn (Text.unpack "  :help | :?                     show this help message")
    outputStrLn (Text.unpack "  :!<command>                    execute a system shell command")
    outputStrLn (Text.unpack "  :paste                         paste mode (empty line or Ctrl-D to finish)")
    outputStrLn (Text.unpack "  quit                           exit the interactive session")

cmdType :: IORef ReplState -> Text -> InputT IO ()
cmdType contextRef exprText = do
    ReplState{replContext = ctx, replPrettyConfig = cfg} <- liftIO (readIORef contextRef)
    case parseExpression exprText of
        Left pe ->
            outputStrLn (Text.unpack (red "✗ " <> renderParseErrorWithSource Nothing (Just exprText) pe))
        Right expr ->
            case synthesize ctx expr of
                Left diag ->
                    outputStrLn (Text.unpack (red "✗ " <> renderTypeDiagnostic Nothing (Just exprText) diag))
                Right (_, inferredType, goals) ->
                    let values = contextValues ctx
                        normType = normalize values inferredType
                     in do
                         outputStrLn (Text.unpack ("  " <> dim ":" <> " " <> magenta (prettyExpressionWith cfg normType)))
                         unless (null goals) $ do
                             outputStrLn (Text.unpack (yellow "⚠" <> " Unsolved goal(s):"))
                             outputStr (Text.unpack (renderGoals goals))

cmdInfo :: IORef ReplState -> Text -> InputT IO ()
cmdInfo contextRef identText = do
    ReplState{replContext = ctx} <- liftIO (readIORef contextRef)
    let ident = Identifier (Text.strip identText)
    case Map.lookup ident (contextData ctx) of
        Just info -> cmdPrintData ident info
        Nothing ->
            case lookupContext ident ctx of
                Left _ ->
                    outputStrLn (Text.unpack (red "✗ " <> "Unknown identifier: '" <> identText <> "'"))
                Right ty -> do
                    outputStrLn (Text.unpack (bold (prettyIdentifier ident) <> " : " <> prettyExpression ty))
                    case Map.lookup ident (contextValues ctx) of
                        Just val -> outputStrLn (Text.unpack ("  = " <> prettyExpression val))
                        Nothing -> pure ()

cmdPrintData :: Identifier -> DataInfo -> InputT IO ()
cmdPrintData ident info = do
    let paramsText =
            Text.intercalate
                " "
                [ ( if vis == Explicit
                      then "("
                      else "{"
                  )
                    <> prettyIdentifier p
                    <> " : "
                    <> prettyExpression ty
                    <> ( if vis == Explicit
                          then ")"
                          else "}"
                  )
                | (vis, p, ty) <- dataParams info
                ]
        universeText = prettyExpression (dataUniverse info)
    outputStrLn (Text.unpack ("data " <> prettyIdentifier ident <> " " <> paramsText <> " : " <> universeText <> " where"))
    mapM_
        (\(cName, cType) -> outputStrLn (Text.unpack ("  " <> prettyIdentifier cName <> " : " <> prettyExpression cType)))
        (dataConstructors info)

cmdBrowse :: IORef ReplState -> InputT IO ()
cmdBrowse contextRef = do
    ReplState{replContext = ctx} <- liftIO (readIORef contextRef)
    outputStrLn (Text.unpack (bold "Data types:"))
    mapM_
        (\(ident, info) ->
            outputStrLn (Text.unpack ("  " <> prettyIdentifier ident <> " : " <> prettyExpression (dataUniverse info))))
        (Map.toList (contextData ctx))
    outputStrLn (Text.unpack (bold "Symbols:"))
    mapM_
        (\(ident, ty) ->
            outputStrLn (Text.unpack ("  " <> prettyIdentifier ident <> " : " <> prettyExpression ty)))
        (Map.toList (contextTypes ctx))

processStatement :: IORef ReplState -> Text -> InputT IO ()
processStatement contextRef input
    | Text.null (Text.strip input) = pure ()
    | otherwise = do
        ReplState{replContext = ctx, replPrettyConfig = cfg} <- liftIO (readIORef contextRef)
        case parseStatement input of
            Left parseError ->
                outputStrLn (Text.unpack (red "✗ " <> renderParseErrorWithSource Nothing (Just input) parseError))
            Right (DataDeclaration name params univ constrs) ->
                case checkDataDeclaration ctx name params univ constrs of
                    Left typeError ->
                        outputStrLn (Text.unpack (red "✗ " <> renderTypeDiagnostic Nothing (Just input) typeError))
                    Right updatedContext -> do
                        let conNames = Text.intercalate ", " (map (prettyIdentifier . fst) constrs)
                        outputStrLn (Text.unpack (green "✓" <> " Defined data " <> bold (prettyIdentifier name) <> " with: " <> cyan conNames))
                        liftIO (modifyIORef' contextRef (\s -> s{replContext = updatedContext, replLastGoals = []}))
            Right (Definition name maybeType bodyTerm) ->
                case checkDefinition ctx name maybeType bodyTerm of
                    Left typeError ->
                        outputStrLn (Text.unpack (red "✗ " <> renderTypeDiagnostic Nothing (Just input) typeError))
                    Right (updatedContext, finalType, goals) -> do
                        if null goals
                            then outputStrLn (Text.unpack (green "✓" <> " Defined " <> bold (prettyIdentifier name) <> " " <> dim ":" <> " " <> magenta (prettyExpressionWith cfg finalType)))
                            else do
                                outputStrLn (Text.unpack (yellow "⚠" <> " Defined " <> bold (prettyIdentifier name) <> " with " <> bold (Text.pack (show (length goals))) <> " goal(s):"))
                                outputStr (Text.unpack (renderGoals goals))
                        liftIO (modifyIORef' contextRef (\s -> s{replContext = updatedContext, replLastGoals = goals}))
            Right (FixityDeclaration assoc prec ops) -> do
                let newCtx = ctx
                        { contextFixities =
                            foldr
                                (\op ex -> Map.insert op (Fixity assoc prec) ex)
                                (contextFixities ctx)
                                ops
                        }
                liftIO (modifyIORef' contextRef (\s -> s{replContext = newCtx, replLastGoals = []}))
                outputStrLn (Text.unpack (green "✓" <> " Declared fixity for " <> cyan (Text.intercalate ", " (map prettyIdentifier ops))))
            Right (Evaluation expression) -> do
                case synthesize ctx expression of
                    Left typeError ->
                        outputStrLn (Text.unpack (red "✗ " <> renderTypeDiagnostic Nothing (Just input) typeError))
                    Right (elaboratedExpr, inferredType, goals) -> do
                        let values = contextValues ctx
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
                                outputStrLn (Text.unpack ("  " <> dim ":" <> " " <> magenta (prettyExpressionWith cfg normType)))
                                outputStrLn (Text.unpack ("  " <> dim "=" <> " " <> bold (green (prettyExpressionWith cfg normExpr))))
                                unless (null goals) $ do
                                    outputStrLn (Text.unpack (yellow "⚠" <> " Unsolved goal(s):"))
                                    outputStr (Text.unpack (renderGoals goals))
                        liftIO (modifyIORef' contextRef (\s -> s{replLastGoals = goals}))

runShellCommand :: String -> IO ()
runShellCommand cmd = do
    cmdResult <- Exception.try (Process.callCommand cmd) :: IO (Either Exception.IOException ())
    case cmdResult of
        Left err -> TextIO.putStrLn (red "✗ " <> "Shell error: " <> Text.pack (show err))
        Right () -> pure ()

loadFileFrom :: Context -> FilePath -> IO (Maybe Context)
loadFileFrom initialContext filePath = do
    fileContentResult <- Exception.try (TextIO.readFile filePath)
    case fileContentResult of
        Left ioException -> do
            let err = ioException :: Exception.IOException
            TextIO.putStrLn (red "✗ " <> "Could not read file '" <> Text.pack filePath <> "': " <> Text.pack (show err))
            pure Nothing
        Right content ->
            case parseProgramWith defaultFixityEnv content of
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
statementIdentifier (FixityDeclaration _ _ _) = Identifier "<fixity>"
statementIdentifier (Evaluation _) = Identifier "<expr>"

statementIdentifiers :: Statement -> [Identifier]
statementIdentifiers (Definition name _ _) = [name]
statementIdentifiers (DataDeclaration name _ _ constrs) = name : map fst constrs
statementIdentifiers (FixityDeclaration _ _ _) = []
statementIdentifiers (Evaluation _) = []

runStatements :: Context -> [Identifier] -> FilePath -> Text -> [Statement] -> IO (Maybe (Context, [Identifier]))
runStatements currentContext accNames _ _ [] = pure (Just (currentContext, reverse accNames))
runStatements currentContext accNames filePath content (statement : remaining) = do
    let name = statementIdentifier statement
    execResult <- Exception.try $ Exception.evaluate $ case statement of
        DataDeclaration dName params univ constrs ->
            case checkDataDeclaration currentContext dName params univ constrs of
                Left typeError ->
                    Left (red "✗ " <> "Type error in data '" <> bold (prettyIdentifier dName) <> "':\n  " <> renderTypeDiagnostic (Just filePath) (Just content) typeError)
                Right updatedContext -> Right updatedContext
        Definition defName maybeType bodyTerm ->
            case checkDefinition currentContext defName maybeType bodyTerm of
                Left typeError ->
                    Left (red "✗ " <> "Type error in definition '" <> bold (prettyIdentifier defName) <> "':\n  " <> renderTypeDiagnostic (Just filePath) (Just content) typeError)
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
        FixityDeclaration assoc prec ops ->
            Right
                ( currentContext
                    { contextFixities =
                        foldr
                            (\op ex -> Map.insert op (Fixity assoc prec) ex)
                            (contextFixities currentContext)
                            ops
                    }
                )
        Evaluation expression ->
            case synthesize currentContext expression of
                Left typeError ->
                    Left (red "✗ " <> "Error in expression: " <> renderTypeDiagnostic Nothing (Just content) typeError)
                Right (_, _, goals) ->
                    if null goals
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
