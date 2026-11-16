{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Diagnostics
    ( renderGoals
    , renderTypeError
    , renderTypeDiagnostic
    ) where

import AST (Identifier (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Diagnostics (formatSourceSnippet)
import Pretty (prettyExpression, prettyIdentifier)
import TypeChecker.Types
    ( Goal (..)
    , TypeDiagnostic (..)
    , TypeError (..)
    )

renderGoals :: [Goal] -> Text
renderGoals goals = Text.concat (map formatGoal goals)
  where
    formatGoal g =
        let nameTag = case goalName g of
                Just ident -> "?" <> prettyIdentifier ident
                Nothing -> "?" <> Text.pack (show (goalId g))
            header = "  \ESC[1;36m[" <> nameTag <> "]\ESC[0m\n"
            target = "    \ESC[1mExpected:\ESC[0m " <> prettyExpression (goalExpected g) <> "\n"
            locals =
                if null (goalLocals g)
                    then ""
                    else
                        "    \ESC[1mContext:\ESC[0m\n"
                            <> Text.concat
                                [ "      " <> prettyIdentifier v <> " : " <> prettyExpression t <> "\n"
                                | (v, t) <- reverse (goalLocals g)
                                ]
         in header <> target <> locals

renderTypeError :: TypeError -> Text
renderTypeError typeError = case typeError of
    UnboundVariable (Identifier name) ->
        "Unbound variable: '" <> name <> "'"
    TypeMismatch expected actual ->
        "Type mismatch:\n  Expected: "
            <> prettyExpression expected
            <> "\n  Actual:   "
            <> prettyExpression actual
    ExpectedFunctionType actual ->
        "Expected a function (Pi) type, but encountered:\n  "
            <> prettyExpression actual
    ExpectedUniverse actual ->
        "Expected a Type universe, but encountered:\n  "
            <> prettyExpression actual
    CannotSynthesizeType term ->
        "Cannot synthesize type for unannotated expression:\n  "
            <> prettyExpression term
            <> "\nProvide an explicit type annotation: (term : Type)"
    CannotMatchOnNonDataType term ->
        "Cannot pattern match on non-data type: " <> prettyExpression term
    ExpectedDataType term ->
        "Expected a record/data value, but encountered: " <> prettyExpression term
    UnknownField (Identifier field) (Identifier recName) ->
        "Unknown field '" <> field <> "' on record '" <> recName <> "'"
    NoInstanceFound domain ->
        "No instance found for " <> prettyExpression domain
    AmbiguousInstance domain names ->
        "Ambiguous instances for " <> prettyExpression domain <> ": " <> Text.intercalate ", " (map prettyIdentifier names)
    NonExhaustivePatternMatch (Identifier dName) missing ->
        "Non-exhaustive pattern match on data type '"
            <> dName
            <> "'. Missing constructor(s):\n  "
            <> Text.intercalate ", " (map prettyIdentifier missing)
    UnknownConstructor (Identifier dName) (Identifier cName) ->
        "Constructor '" <> cName <> "' does not belong to data type '" <> dName <> "'"
    NonStrictlyPositive (Identifier dName) (Identifier cName) ->
        "Non-strictly positive occurrence of '"
            <> dName
            <> "' in constructor '"
            <> cName
            <> "'"
    NonTerminatingDefinition (Identifier name) ->
        "Non-terminating definition: recursive calls to '"
            <> name
            <> "' do not apply a structurally decreasing argument"
    ArityMismatch (Identifier cName) expected actual ->
        "Constructor '"
            <> cName
            <> "' expects "
            <> Text.pack (show expected)
            <> " arguments, but found "
            <> Text.pack (show actual)
    OccursCheckFailed i term ->
        "Occurs check failed: ?" <> Text.pack (show i) <> " occurs in " <> prettyExpression term
    ScopeEscapeFailed i (Identifier var) term ->
        "Scope escape error: Variable '"
            <> var
            <> "' cannot appear in the solution for ?"
            <> Text.pack (show i)
            <> " := "
            <> prettyExpression term
            <> " because it was bound outside the metavariable's scope."
    UnsolvedMetavariable i ->
        "Unsolved metavariable: ?" <> Text.pack (show i)
    UniverseInconsistency msg ->
        "Universe inconsistency: " <> msg

renderTypeDiagnostic :: Maybe FilePath -> Maybe Text -> TypeDiagnostic -> Text
renderTypeDiagnostic mFile mSource diag =
    let tracePart =
            if null (diagTrace diag)
                then ""
                else "  " <> Text.intercalate "\n  " (diagTrace diag) <> "\n"
        snippetPart = case (mSource, diagSpan diag) of
            (Just src, Just sp) -> formatSourceSnippet mFile src sp (renderTypeError (diagError diag))
            _ -> renderTypeError (diagError diag)
     in tracePart <> snippetPart
