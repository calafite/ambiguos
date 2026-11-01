module Automata.Parser (
    parseRegex,
) where

import Automata.Types

parseRegex :: String -> Either String Regex
parseRegex input = case parseUnion input of
    Right (regex, "") -> Right regex
    Right (_, leftover) -> Left ("Unexpected trailing characters: " ++ leftover)
    Left err -> Left err

parseUnion :: String -> Either String (Regex, String)
parseUnion input = do
    (left, rest) <- parseConcat input
    case rest of
        ('|' : remaining) -> do
            (right, afterRight) <- parseUnion remaining
            pure (Union left right, afterRight)
        _ -> pure (left, rest)

parseConcat :: String -> Either String (Regex, String)
parseConcat input = do
    (first, rest) <- parseStar input
    case rest of
        [] -> pure (first, [])
        (')' : _) -> pure (first, rest)
        ('|' : _) -> pure (first, rest)
        _ -> do
            (second, afterSecond) <- parseConcat rest
            pure (Concat first second, afterSecond)

parseStar :: String -> Either String (Regex, String)
parseStar input = do
    (base, rest) <- parseAtom input
    case rest of
        ('*' : remaining) -> pure (Star base, remaining)
        _ -> pure (base, rest)

parseAtom :: String -> Either String (Regex, String)
parseAtom input = case input of
    [] -> pure (Epsilon, [])
    ('(' : rest) -> do
        (inner, afterInner) <- parseUnion rest
        case afterInner of
            (')' : remaining) -> pure (inner, remaining)
            _ -> Left "Missing closing parenthesis"
    (char : rest)
        | char `notElem` ['*', '|', '(', ')'] -> pure (Literal char, rest)
        | otherwise -> Left ("Unexpected character: " ++ [char])
