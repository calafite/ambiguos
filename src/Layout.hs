{-# LANGUAGE OverloadedStrings #-}

module Layout (
    insertLayout
) where

import Lexer (PosToken (..), Token (..))
import Diagnostics (SourcePos (..))

-- | Insert virtual '{', '}', ';' tokens to implement the Haskell offside rule.
insertLayout :: [PosToken] -> [PosToken]
insertLayout tokens = go [] 1 tokens
  where
    -- stack: columns and whether the block was inserted by layout (top = head)
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
                        ++ go ((ncol, True) : stack') line ts
                TokenKeywordWhere | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go ((ncol, True) : stack') line ts
                TokenKeywordDo | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go ((ncol, True) : stack') line ts
                TokenKeywordOf | not (nextIsBrace ts) ->
                    let ncol = nextTokenCol ts (col + 1)
                     in [t, PosToken pos TokenLeftBrace]
                        ++ go ((ncol, True) : stack') line ts
                -- `in` closes the nearest virtual `let` block before the
                -- parser sees the keyword. Explicit braces remain explicit.
                TokenKeywordIn | closesVirtualBlock stack' ->
                    PosToken pos TokenRightBrace : t : go (drop 1 stack') line ts
                -- Explicit '{': push its column
                TokenLeftBrace -> t : go ((col, False) : stack') line ts
                -- Explicit '}': pop one level
                TokenRightBrace -> t : go (drop 1 stack') line ts
                -- New line at same column as top of stack: insert ';'
                _ | isNewLine && case stack' of ((c, _) : _) -> col == c; _ -> False ->
                    PosToken pos TokenSemicolon : t : go stack' line ts
                _ -> t : go stack' line ts

            in closeTokens ++ result

    -- Close layout blocks whose column > col. Returns (virtual '}' tokens, remaining stack).
    closeBlocks :: SourcePos -> [(Int, Bool)] -> Int -> ([PosToken], [(Int, Bool)])
    closeBlocks _ [] _ = ([], [])
    closeBlocks pos ((c, virtual) : cs) col
        | virtual && col < c =
            let (ts, rest) = closeBlocks pos cs col
             in (PosToken pos TokenRightBrace : ts, rest)
        | otherwise = ([], (c, virtual) : cs)

    closesVirtualBlock :: [(Int, Bool)] -> Bool
    closesVirtualBlock ((_, True) : _) = True
    closesVirtualBlock _ = False

    -- Column of next token, or default if none
    nextTokenCol [] def = def
    nextTokenCol (PosToken p _ : _) _ = posColumn p

    -- Check if next token is explicit '{'
    nextIsBrace [] = False
    nextIsBrace (PosToken _ TokenLeftBrace : _) = True
    nextIsBrace _ = False
