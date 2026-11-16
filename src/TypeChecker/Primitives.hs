{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Primitives
    ( primitiveBindings
    , primitiveTypes
    , primitiveValues
    , primitiveOpType
    , numericOperator
    , numericKind
    , numericPrimitive
    , coerceNumeric
    , isSuccessorExpression
    , intSuccessorExpression
    ) where

import AST
    ( Expression (..)
    , Identifier (..)
    , Literal (..)
    , PrimOp (..)
    , PrimType (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

primitiveBindings :: [(Identifier, PrimOp)]
primitiveBindings =
    [ (Identifier "primNatToInt", NatToInt)
    , (Identifier "primIntAdd", IntAdd), (Identifier "primIntSub", IntSub), (Identifier "primIntMul", IntMul), (Identifier "primIntPow", IntPow)
    , (Identifier "primIntDiv", IntDiv), (Identifier "primIntMod", IntMod), (Identifier "primIntNeg", IntNeg)
    , (Identifier "primIntEq", IntEq), (Identifier "primIntNeq", IntNeq), (Identifier "primIntLt", IntLt), (Identifier "primIntLe", IntLe), (Identifier "primIntGt", IntGt), (Identifier "primIntGe", IntGe), (Identifier "primBoolEq", BoolEq)
    , (Identifier "primIntFold", IntFold)
    , (Identifier "primFloatAdd", FloatAdd), (Identifier "primFloatSub", FloatSub), (Identifier "primFloatMul", FloatMul), (Identifier "primFloatDiv", FloatDiv), (Identifier "primFloatEq", FloatEq)
    , (Identifier "primStringAppend", StringAppend), (Identifier "primStringEq", StringEq), (Identifier "primStringLength", StringLength)
    , (Identifier "primCharEq", CharEq), (Identifier "primCharToInt", CharToInt), (Identifier "primIntToChar", IntToChar)
    ]

primitiveTypes :: Map Identifier Expression
primitiveTypes = Map.fromList [(name, primitiveOpType operation) | (name, operation) <- primitiveBindings]

primitiveValues :: Map Identifier Expression
primitiveValues = Map.fromList [(name, PrimOp operation) | (name, operation) <- primitiveBindings]

primitiveOpType :: PrimOp -> Expression
primitiveOpType operation = case operation of
    NatToInt -> unary NatType (PrimType PTInt)
    IntNeg -> unary (PrimType PTInt) (PrimType PTInt)
    FloatNeg -> unary (PrimType PTFloat) (PrimType PTFloat)
    IntAdd -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntSub -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntMul -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntPow -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntDiv -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntMod -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntEq -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    IntNeq -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    IntLt -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    IntLe -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    IntGt -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    IntGe -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    BoolEq -> binary (Variable (Identifier "Bool")) (Variable (Identifier "Bool")) (Variable (Identifier "Bool"))
    FloatAdd -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat)
    FloatSub -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat)
    FloatMul -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat)
    FloatDiv -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat)
    FloatEq -> binary (PrimType PTFloat) (PrimType PTFloat) (Variable (Identifier "Bool"))
    FloatLt -> binary (PrimType PTFloat) (PrimType PTFloat) (Variable (Identifier "Bool"))
    FloatLe -> binary (PrimType PTFloat) (PrimType PTFloat) (Variable (Identifier "Bool"))
    StringAppend -> binary (PrimType PTString) (PrimType PTString) (PrimType PTString)
    StringEq -> binary (PrimType PTString) (PrimType PTString) (Variable (Identifier "Bool"))
    CharEq -> binary (PrimType PTChar) (PrimType PTChar) (Variable (Identifier "Bool"))
    IntToFloat -> unary (PrimType PTInt) (PrimType PTFloat)
    FloatToInt -> unary (PrimType PTFloat) (PrimType PTInt)
    FloatTruncate -> unary (PrimType PTFloat) (PrimType PTInt)
    CharToInt -> unary (PrimType PTChar) (PrimType PTInt)
    IntToChar -> unary (PrimType PTInt) (PrimType PTChar)
    StringLength -> unary (PrimType PTString) NatType
    StringToList -> unary (PrimType PTString) (Variable (Identifier "List"))
    ListToString -> unary (Variable (Identifier "List")) (PrimType PTString)
    IntToString -> unary (PrimType PTInt) (PrimType PTString)
    FloatToString -> unary (PrimType PTFloat) (PrimType PTString)
    CharToString -> unary (PrimType PTChar) (PrimType PTString)
    FloatSqrt -> unary (PrimType PTFloat) (PrimType PTFloat)
    FloatSin -> unary (PrimType PTFloat) (PrimType PTFloat)
    FloatCos -> unary (PrimType PTFloat) (PrimType PTFloat)
    FloatExp -> unary (PrimType PTFloat) (PrimType PTFloat)
    FloatLog -> unary (PrimType PTFloat) (PrimType PTFloat)
    StringIndex -> binary (PrimType PTString) NatType (Variable (Identifier "Maybe"))
    StringSlice -> binary (PrimType PTString) (PrimType PTInt) (PrimType PTString)
    IntFold -> Pi Implicit (Identifier "A") (Universe (UFixed (-1))) (Pi Explicit (Identifier "n") (PrimType PTInt) (Pi Explicit (Identifier "z") (Variable (Identifier "A")) (Pi Explicit (Identifier "step") (Pi Explicit (Identifier "_") (PrimType PTInt) (Pi Explicit (Identifier "_") (Variable (Identifier "A")) (Variable (Identifier "A")))) (Variable (Identifier "A")))))
  where
    unary domain codomain = Pi Explicit (Identifier "_") domain codomain
    binary left right codomain = Pi Explicit (Identifier "_") left (Pi Explicit (Identifier "_") right codomain)

numericOperator :: Identifier -> Bool
numericOperator name = name `elem`
    map Identifier ["+", "-", "*", "/", "^", "==", "/=", "<", "<=", ">", ">=", "++"]

numericKind :: Expression -> Maybe PrimType
numericKind ty = case ty of
    PrimType p -> Just p
    _ -> Nothing

numericPrimitive :: Identifier -> PrimType -> Maybe PrimOp
numericPrimitive name kind = case (name, kind) of
    (Identifier "+", PTInt) -> Just IntAdd
    (Identifier "-", PTInt) -> Just IntSub
    (Identifier "*", PTInt) -> Just IntMul
    (Identifier "/", PTInt) -> Just IntDiv
    (Identifier "^", PTInt) -> Just IntPow
    (Identifier "==", PTInt) -> Just IntEq
    (Identifier "<", PTInt) -> Just IntLt
    (Identifier "<=", PTInt) -> Just IntLe
    (Identifier ">", PTInt) -> Just IntGt
    (Identifier ">=", PTInt) -> Just IntGe
    (Identifier "/=", PTInt) -> Just IntNeq
    (Identifier "==", PTString) -> Just StringEq
    (Identifier "/=", PTString) -> Just StringEq
    (Identifier "++", PTString) -> Just StringAppend
    (Identifier "==", PTChar) -> Just CharEq
    (Identifier "/=", PTChar) -> Just CharEq
    (Identifier "+", PTFloat) -> Just FloatAdd
    (Identifier "-", PTFloat) -> Just FloatSub
    (Identifier "*", PTFloat) -> Just FloatMul
    (Identifier "/", PTFloat) -> Just FloatDiv
    (Identifier "==", PTFloat) -> Just FloatEq
    (Identifier "<", PTFloat) -> Just FloatLt
    (Identifier "<=", PTFloat) -> Just FloatLe
    (Identifier "/=", PTFloat) -> Just FloatEq
    _ -> Nothing

coerceNumeric :: PrimType -> Expression -> Expression -> Expression
coerceNumeric target expr fromType = case (target, fromType) of
    (PTInt, NatType) -> Application Explicit (PrimOp NatToInt) expr
    (PTFloat, NatType) -> Application Explicit (PrimOp IntToFloat)
        (Application Explicit (PrimOp NatToInt) expr)
    (PTFloat, PrimType PTInt) -> Application Explicit (PrimOp IntToFloat) expr
    _ -> expr

isSuccessorExpression :: Expression -> Bool
isSuccessorExpression Succ = True
isSuccessorExpression (Located _ Succ) = True
isSuccessorExpression (Variable (Identifier "successor")) = True
isSuccessorExpression _ = False

intSuccessorExpression :: Expression -> Expression
intSuccessorExpression value =
    Application Explicit
        (Application Explicit (PrimOp IntAdd) value)
        (Literal (LitInt 1))
