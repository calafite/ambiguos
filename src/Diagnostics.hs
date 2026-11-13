{-# LANGUAGE OverloadedStrings #-}

module Diagnostics (
    SourcePos (..),
    SourceSpan (..),
    formatSourceSnippet,
) where

import Data.Text (Text)
import qualified Data.Text as Text

data SourcePos = SourcePos
    { posLine :: !Int
    , posColumn :: !Int
    } deriving (Eq, Ord, Show)

data SourceSpan = SourceSpan
    { spanStart :: !SourcePos
    , spanEnd   :: !SourcePos
    } deriving (Eq, Ord, Show)

formatSourceSnippet :: Maybe FilePath -> Text -> SourceSpan -> Text -> Text
formatSourceSnippet mFile source (SourceSpan start end) msg =
    let lineNum = posLine start
        startCol = posColumn start
        endCol = if posLine end == lineNum then posColumn end else startCol
        linesList = Text.lines source
        lineContent =
            if lineNum > 0 && lineNum <= length linesList
                then linesList !! (lineNum - 1)
                else ""
        filePrefix = case mFile of
            Just fp -> Text.pack fp <> ":" <> Text.pack (show lineNum) <> ":" <> Text.pack (show startCol) <> ":\n"
            Nothing -> "Line " <> Text.pack (show lineNum) <> ", col " <> Text.pack (show startCol) <> ":\n"
        gutter = Text.pack (show lineNum) <> " │ "
        gutterSpace = Text.replicate (Text.length (Text.pack (show lineNum))) " " <> " │ "
        colIndex = max 0 (min (startCol - 1) (Text.length lineContent))
        pointerLen = max 1 (endCol - startCol)
        pointer = Text.replicate colIndex " " <> Text.replicate pointerLen "^"
     in filePrefix
            <> "  "
            <> gutter
            <> lineContent
            <> "\n"
            <> "  "
            <> gutterSpace
            <> pointer
            <> "\n"
            <> "  "
            <> msg
