{-# LANGUAGE OverloadedStrings #-}

module Layout (
    insertLayout
) where

import Lexer (PosToken (..), Token (..))
import Diagnostics (SourcePos (..))

-- | Layout triggers that open a new layout block when followed by indented content.
layoutTriggers :: [Token]
layoutTriggers = [TokenKeywordOf, TokenKeywordWhere, TokenKeywordLet, TokenKeywordDo]

-- | Insert virtual '{', '}', ';' tokens to implement the Haskell offside rule.
insertLayout :: [PosToken] -> [PosToken]
insertLayout tokens = go [] 1 tokens
  where
    -- stack: columns of active layout blocks (top = head)
    -- prevLine: line number of the previous token
    go _ _ [] = []
    go stack prevLine (t : ts) =
        let pos = tokenPos t
            col = posColumn pos
            line = posLine pos
            isNewLine = line > prevLine

            -- Close layout blocks whose column is strictly greater than col
            (closeTokens, stack') = closeBlocks pos stack col

            result = case tokenValue t of
                -- Layout trigger: if not followed by explicit '{', open layout block
                TokenKeywordLet | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go (ncol : stack') line ts
                TokenKeywordWhere | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go (ncol : stack') line ts
                TokenKeywordDo | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go (ncol : stack') line ts
                TokenKeywordOf | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go (ncol : stack') line ts
                -- Explicit '{': push its column
                TokenLeftBrace -> t : go (col : stack') line ts
                -- Explicit '}': pop one level
                TokenRightBrace -> t : go (drop 1 stack') line ts
                -- New line at same column as top of stack: insert ';'
                _ | isNewLine && case stack' of (c : _) -> col == c; _ -> False ->
                    PosToken pos TokenSemicolon : t : go stack' line ts
                _ -> t : go stack' line ts

            in closeTokens ++ result

    -- Close layout blocks whose column > col. Returns (virtual '}' tokens, remaining stack).
    closeBlocks :: SourcePos -> [Int] -> Int -> ([PosToken], [Int])
    closeBlocks _ [] _ = ([], [])
    closeBlocks pos (c : cs) col =
        if col < c
            then let (ts, rest) = closeBlocks pos cs col
                in (PosToken pos TokenRightBrace : ts, rest)
            else ([], c : cs)

    -- Column of next token, or default if none
    nextTokenCol [] def = def
    nextTokenCol (PosToken p _ : _) _ = posColumn p

    -- Check if next token is explicit '{'
    nextIsBrace [] = False
    nextIsBrace (PosToken _ TokenLeftBrace : _) = True
    nextIsBrace _ = False
