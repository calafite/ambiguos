{-# LANGUAGE OverloadedStrings #-}

module Pretty
    ( PrettyConfig (..)
    , defaultPrettyConfig
    , prettyExpression
    , prettyExpressionWith
    , prettyIdentifier
    , prettyWithPrecedence
    ) where

import AST
    ( Associativity (..)
    , CaseBranch (..)
    , Expression (..)
    , Fixity (..)
    , Guard (..)
    , GuardedRhs (..)
    , Identifier (..)
    , Literal (..)
    , Pattern (..)
    , PrimOp (..)
    , PrimType (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Data.Text (Text)
import qualified Data.Text as Text
import Parser (FixityEnv, defaultFixityEnv, fixityOf)

data Precedence
    = TopLevelPrecedence
    | AnnotationPrecedence
    | LambdaPrecedence
    | ArrowPrecedence
    | ApplicationPrecedence
    | AtomicPrecedence
    deriving (Eq, Ord, Show)

precLevel :: Precedence -> Int
precLevel TopLevelPrecedence = 0
precLevel AnnotationPrecedence = 1
precLevel LambdaPrecedence = 2
precLevel ArrowPrecedence = 3
precLevel ApplicationPrecedence = 7
precLevel AtomicPrecedence = 10

data PrettyConfig = PrettyConfig
    { prettyShowImplicits :: !Bool
    , prettyFixities      :: !FixityEnv
    }
    deriving (Eq, Show)

defaultPrettyConfig :: PrettyConfig
defaultPrettyConfig = PrettyConfig False defaultFixityEnv

prettyExpression :: Expression -> Text
prettyExpression = prettyExpressionWith defaultPrettyConfig

prettyExpressionWith :: PrettyConfig -> Expression -> Text
prettyExpressionWith c = prettyWithConfig c 0

prettyWithPrecedence :: PrettyConfig -> Precedence -> Expression -> Text
prettyWithPrecedence c = prettyWithConfig c . precLevel

prettyWithConfig :: PrettyConfig -> Int -> Expression -> Text
prettyWithConfig c p e
    | Just n <- peanoToInteger e = Text.pack (show n)
    | Just xs <- pairToElements e = tupleText c xs
    | Just xs <- pairTypeToElements e = tupleText c xs
    | Just xs <- peanoListToElements e = listText c xs
    | otherwise = case e of
        Tuple xs -> tupleText c xs
        Located _ x -> prettyWithConfig c p x
        Variable x
            | x == Identifier "unit" -> "()"
            | otherwise -> prettyIdentifier x
        Universe x -> prettyUniverseLevel x
        Identity -> "Id"
        Reflexivity -> "refl"
        J -> "J"
        VoidType -> "Void"
        Abort -> "abort"
        Literal x -> parenthesizeIf (p >= 7 && isNegativeLiteral x) (prettyLiteral x)
        PrimType x -> prettyPrimType x
        PrimOp x -> maybe (prettyPrimOp x) (\s -> "(" <> s <> ")") (primitiveSymbol x)
        Hole Nothing -> "?"
        Hole (Just (Identifier x)) -> "?" <> x
        MetaVar i -> "?" <> Text.pack (show i)
        Projection x f -> prettyWithConfig c p x <> "." <> prettyIdentifier f
        RecordLiteral n fs ->
            prettyIdentifier n
                <> " { "
                <> Text.intercalate ", " [prettyIdentifier f <> " = " <> prettyWithConfig c 0 x | (f, x) <- fs]
                <> " }"
        Case t _ bs ->
            "case "
                <> prettyWithConfig c 0 t
                <> " of { "
                <> Text.intercalate "; " [prettyCaseBranch q | q <- bs]
                <> " }"
        Annotation x t -> parenthesizeIf (p > 1) (prettyWithConfig c 3 x <> " :: " <> prettyWithConfig c 0 t)
        Lambda v n mt b -> parenthesizeIf (p > 2) (lambdaText c v n mt b)
        Application Explicit (Application Explicit (PrimOp op) a) b
            | Just s <- primitiveSymbol op ->
                prettyInfixApp c (prettyFixities c) (Identifier s) a b p
        Application Explicit (PrimOp op) a
            | Just s <- primitiveSymbol op ->
                parenthesizeIf (p > 7) ("(" <> s <> ") " <> prettyWithConfig c 10 a)
        Application Explicit (Application Explicit (Variable op) a) b
            | isSymbolic op ->
                prettyInfixApp c (prettyFixities c) op a b p
        Application Explicit f a ->
            parenthesizeIf (p > 7) (prettyWithConfig c 7 f <> " " <> prettyWithConfig c 10 a)
        Application Implicit f a
            | prettyShowImplicits c ->
                parenthesizeIf (p > 7) (prettyWithConfig c 7 f <> " {" <> prettyWithConfig c 0 a <> "}")
            | otherwise ->
                prettyWithConfig c p f
        Application Instance f a ->
            parenthesizeIf (p > 7) (prettyWithConfig c 7 f <> " {{" <> prettyWithConfig c 0 a <> "}}")
        Pi Explicit (Identifier "_") d r ->
            parenthesizeIf (p > 3) (prettyWithConfig c 7 d <> " -> " <> prettyWithConfig c 3 r)
        Pi Explicit n d r ->
            parenthesizeIf (p > 3) ("(" <> prettyIdentifier n <> " :: " <> prettyWithConfig c 0 d <> ") -> " <> prettyWithConfig c 3 r)
        Pi Implicit n d r ->
            parenthesizeIf (p > 3) ("{" <> prettyIdentifier n <> " :: " <> prettyWithConfig c 0 d <> "} -> " <> prettyWithConfig c 3 r)
        Pi Instance n d r ->
            parenthesizeIf (p > 3) ("{{" <> prettyIdentifier n <> " :: " <> prettyWithConfig c 0 d <> "}} -> " <> prettyWithConfig c 3 r)
        Let n mt d b ->
            parenthesizeIf (p > 2) ("let " <> prettyIdentifier n <> maybe "" (\t -> " :: " <> prettyWithConfig c 0 t) mt <> " = " <> prettyWithConfig c 0 d <> " in " <> prettyWithConfig c 0 b)
        Case t mm bs ->
            parenthesizeIf (p > 2) ("case " <> prettyWithConfig c 0 t <> motive mm <> " of { " <> Text.intercalate " ; " (map branch bs) <> " }")
  where
    motive Nothing = ""
    motive (Just (n, t)) = " as " <> prettyIdentifier n <> " return " <> prettyWithConfig c 0 t

    branch (CaseBranch pat rhss _) =
        prettyPattern pat <> " -> " <> Text.intercalate " | " [prettyGuardedRhs r | r <- rhss]
    prettyGuardedRhs (GuardedRhs [] body) = prettyWithConfig c 0 body
    prettyGuardedRhs (GuardedRhs guards body) =
        Text.intercalate " && " [prettyGuard g | g <- guards] <> " -> " <> prettyWithConfig c 0 body
    prettyGuard (BoolGuard e) = prettyWithConfig c 0 e
    prettyGuard (PatGuard p e) = prettyPattern p <> " <- " <> prettyWithConfig c 0 e

lambdaText :: PrettyConfig -> Visibility -> Identifier -> Maybe Expression -> Expression -> Text
lambdaText c v n mt b = "\\" <> binder <> " -> " <> prettyWithConfig c 0 b
  where
    binder = case (v, mt) of
        (Explicit, Nothing) -> prettyIdentifier n
        (Explicit, Just t) -> "(" <> prettyIdentifier n <> " : " <> prettyWithConfig c 0 t <> ")"
        (Implicit, Nothing) -> "{" <> prettyIdentifier n <> "}"
        (Implicit, Just t) -> "{" <> prettyIdentifier n <> " : " <> prettyWithConfig c 0 t <> "}"
        (Instance, Nothing) -> "{{" <> prettyIdentifier n <> "}}"
        (Instance, Just t) -> "{{" <> prettyIdentifier n <> " : " <> prettyWithConfig c 0 t <> "}}"

tupleText :: PrettyConfig -> [Expression] -> Text
tupleText c xs = "(" <> Text.intercalate ", " (map (prettyWithConfig c 0) xs) <> ")"

listText :: PrettyConfig -> [Expression] -> Text
listText c xs = "[" <> Text.intercalate ", " (map (prettyWithConfig c 0) xs) <> "]"

parenthesizeIf :: Bool -> Text -> Text
parenthesizeIf True x = "(" <> x <> ")"
parenthesizeIf False x = x

prettyIdentifier :: Identifier -> Text
prettyIdentifier i@(Identifier n)
    | isSymbolic i = "(" <> n <> ")"
    | otherwise = n

prettyPattern :: Pattern -> Text
prettyPattern PatWild = "_"
prettyPattern (PatVar n) = prettyIdentifier n
prettyPattern (PatAs n p) = prettyIdentifier n <> "@" <> prettyPattern p
prettyPattern (PatLit n) = prettyLiteral n
prettyPattern (PatCon (Identifier ":") [x, xs]) = prettyPattern x <> " : " <> prettyPattern xs
prettyPattern (PatCon n xs) = Text.unwords (prettyIdentifier n : map (\x -> "(" <> prettyPattern x <> ")") xs)
prettyPattern (PatTuple xs) = tupleTextPattern xs
prettyPattern (PatList xs) = "[" <> Text.intercalate ", " (map prettyPattern xs) <> "]"

prettyCaseBranch :: CaseBranch -> Text
prettyCaseBranch (CaseBranch pat rhss _) =
    prettyPattern pat <> " -> " <> Text.intercalate " | " [prettyGuardedRhs r | r <- rhss]
  where
    prettyGuardedRhs (GuardedRhs [] body) = prettyWithConfig (PrettyConfig False defaultFixityEnv) 0 body
    prettyGuardedRhs (GuardedRhs guards body) =
        Text.intercalate " && " [prettyGuard g | g <- guards] <> " -> " <> prettyWithConfig (PrettyConfig False defaultFixityEnv) 0 body
    prettyGuard (BoolGuard e) = prettyWithConfig (PrettyConfig False defaultFixityEnv) 0 e
    prettyGuard (PatGuard p e) = prettyPattern p <> " <- " <> prettyWithConfig (PrettyConfig False defaultFixityEnv) 0 e

tupleTextPattern :: [Pattern] -> Text
tupleTextPattern xs = "(" <> Text.intercalate ", " (map prettyPattern xs) <> ")"

prettyLiteral :: Literal -> Text
prettyLiteral (LitInt n) = Text.pack (show n)
prettyLiteral (LitFloat n) = Text.pack (show n)
prettyLiteral (LitChar x) = Text.pack (show x)
prettyLiteral (LitString x) = "\"" <> x <> "\""

isNegativeLiteral :: Literal -> Bool
isNegativeLiteral (LitInt n) = n < 0
isNegativeLiteral _ = False

prettyPrimType :: PrimType -> Text
prettyPrimType PTInt = "Int"
prettyPrimType PTFloat = "Float"
prettyPrimType PTChar = "Char"

prettyUniverseLevel :: UniverseLevel -> Text
prettyUniverseLevel (UFixed (-1)) = "Type"
prettyUniverseLevel (UFixed n) = "Type " <> Text.pack (show n)
prettyUniverseLevel (UVar n) = "Type ?" <> Text.pack (show n)
prettyUniverseLevel (UMax a b) = "Type (max " <> prettyUniverseLevel a <> " " <> prettyUniverseLevel b <> ")"
prettyUniverseLevel (USucc a) = "Type (succ " <> prettyUniverseLevel a <> ")"

prettyPrimOp :: PrimOp -> Text
prettyPrimOp op = "prim" <> Text.pack (drop 3 (show op))

primitiveSymbol :: PrimOp -> Maybe Text
primitiveSymbol IntAdd = Just "+"
primitiveSymbol IntSub = Just "-"
primitiveSymbol IntMul = Just "*"
primitiveSymbol IntDiv = Just "/"
primitiveSymbol IntPow = Just "^"
primitiveSymbol IntEq = Just "=="
primitiveSymbol IntNeq = Just "/="
primitiveSymbol IntLt = Just "<"
primitiveSymbol IntLe = Just "<="
primitiveSymbol IntGt = Just ">"
primitiveSymbol IntGe = Just ">="
primitiveSymbol StringAppend = Just "++"
primitiveSymbol _ = Nothing

isSymbolic :: Identifier -> Bool
isSymbolic (Identifier n) = case Text.uncons n of
    Just (x, _) -> x `elem` ("+-*/<>=!&|$%^~." :: String)
    Nothing -> False

peanoToInteger :: Expression -> Maybe Integer
peanoToInteger _ = Nothing

stripImplicit :: Expression -> Expression
stripImplicit (Application Implicit x _) = stripImplicit x
stripImplicit x = x

peanoListToElements :: Expression -> Maybe [Expression]
peanoListToElements x = case stripImplicit x of
    Variable (Identifier "[]") -> Just []
    Application Explicit (Application Explicit h a) r
        | stripImplicit h == Variable (Identifier ":") -> (a :) <$> peanoListToElements r
    Located _ y -> peanoListToElements y
    _ -> Nothing

pairToElements :: Expression -> Maybe [Expression]
pairToElements x = case stripImplicit x of
    Application Explicit (Application Explicit h a) b
        | stripImplicit h == Variable (Identifier "pair") -> Just (a : maybe [b] id (pairToElements b))
    _ -> Nothing

pairTypeToElements :: Expression -> Maybe [Expression]
pairTypeToElements x = case stripImplicit x of
    Application Explicit (Application Explicit h a) b
        | stripImplicit h == Variable (Identifier "Pair") -> Just (a : maybe [b] id (pairTypeToElements b))
    _ -> Nothing

prettyInfixApp :: PrettyConfig -> FixityEnv -> Identifier -> Expression -> Expression -> Int -> Text
prettyInfixApp c env op a b p =
    parenthesizeIf (p > q) (infixOperand c env q assoc True a <> " " <> n <> " " <> rightText)
  where
    Fixity assoc q = fixityOf env op
    Identifier n = op
    rightText = case infixParts b of
        Just _ -> "(" <> prettyWithConfig c q b <> ")"
        _ -> infixOperand c env q assoc False b

infixParts :: Expression -> Maybe (Expression, Expression)
infixParts x = case stripExpr x of
    Application Explicit f b -> case stripExpr f of
        Application Explicit op a
            | Variable _ <- stripExpr op -> Just (a, b)
        _ -> Nothing
    _ -> Nothing

stripExpr :: Expression -> Expression
stripExpr (Located _ x) = stripExpr x
stripExpr x = x

infixOperand :: PrettyConfig -> FixityEnv -> Int -> Associativity -> Bool -> Expression -> Text
infixOperand c env q assoc left x = case x of
    Application Explicit (Application Explicit (Variable op) a) b ->
        let Fixity assoc2 q2 = fixityOf env op
            rendered = prettyInfixApp c env op a b q
            needs = if left
                then q2 < q || (q2 == q && not (assoc == AssocLeft && assoc2 == AssocLeft))
                else q2 <= q && not (assoc == AssocRight && assoc2 == AssocRight)
         in if needs then "(" <> rendered <> ")" else rendered
    _ -> prettyWithConfig c q x
