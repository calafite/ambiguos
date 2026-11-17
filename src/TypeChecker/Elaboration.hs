{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Elaboration
    ( identityType
    , reflexivityType
    , jType
    , abortType
    , tupleValue
    , checkIsType
    , numericBinary
    , synthesizeElab
    , checkElab
    ) where

import AST
    ( Expression (..)
    , Identifier (..)
    , Literal (..)
    , PrimOp (..)
    , PrimType (..)
    , RecordField (..)
    , RecordInfo (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad.State.Strict (gets, modify)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Evaluation (evaluateWeakHeadNormalForm)
import Substitution (substitute)
import TypeChecker.Meta
    ( freshMeta
    , freshMetaId
    , recordMeta
    , solvePattern
    , unfoldApp
    , zonk
    )
import TypeChecker.PatternCheck (checkCaseBranches)
import TypeChecker.Primitives
    ( coerceNumeric
    , numericKind
    , numericOperator
    , numericPrimitive
    , primitiveOpType
    )
import TypeChecker.Types
    ( Context (..)
    , Elab
    , ElabState (..)
    , TypeError (..)
    , UnivConstraint (..)
    , extendContextDefinition
    , extendContextType
    , liftEither
    , localSpan
    , lookupContext
    , throwError
    )

import TypeChecker.Unify (instantiateLeadingImplicits, unify)
import TypeChecker.Universe
    ( addUnivConstraint
    , extractUniverseLevel
    , freshUnivVar
    )

listCharType :: Expression
listCharType = Application Explicit (Variable (Identifier "List")) (PrimType PTChar)

identityType, reflexivityType, jType, abortType :: Expression
identityType =
    Pi
        Explicit
        (Identifier "A")
        (Universe (UFixed (-1)))
        ( Pi
            Explicit
            (Identifier "_")
            (Variable (Identifier "A"))
            (Pi Explicit (Identifier "_") (Variable (Identifier "A")) (Universe (UFixed (-1))))
        )
reflexivityType =
    Pi
        Explicit
        (Identifier "A")
        (Universe (UFixed (-1)))
        ( Pi
            Explicit
            (Identifier "x")
            (Variable (Identifier "A"))
            ( Application
                Explicit
                ( Application
                    Explicit
                    (Application Explicit Identity (Variable (Identifier "A")))
                    (Variable (Identifier "x"))
                )
                (Variable (Identifier "x"))
            )
        )
jType =
    Pi Explicit (Identifier "A") (Universe (UFixed (-1)))
        $ Pi Explicit (Identifier "x") (Variable (Identifier "A"))
        $ Pi Explicit (Identifier "P") motiveType
        $ Pi Explicit (Identifier "d") baseCaseType
        $ Pi Explicit (Identifier "y") (Variable (Identifier "A"))
        $ Pi Explicit (Identifier "p") proofType codomainType
  where
    motiveType =
        Pi
            Explicit
            (Identifier "y")
            (Variable (Identifier "A"))
            ( Pi
                Explicit
                (Identifier "_")
                (Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y")))
                (Universe (UFixed (-1)))
            )
    baseCaseType =
        Application
            Explicit
            (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "x")))
            (Application Explicit (Application Explicit Reflexivity (Variable (Identifier "A"))) (Variable (Identifier "x")))
    proofType =
        Application Explicit (Application Explicit (Application Explicit Identity (Variable (Identifier "A"))) (Variable (Identifier "x"))) (Variable (Identifier "y"))
    codomainType =
        Application Explicit (Application Explicit (Variable (Identifier "P")) (Variable (Identifier "y"))) (Variable (Identifier "p"))
abortType =
    Pi
        Explicit
        (Identifier "A")
        (Universe (UFixed (-1)))
        (Pi Explicit (Identifier "_") VoidType (Variable (Identifier "A")))

tupleValue :: [Expression] -> Expression
tupleValue [] = Variable (Identifier "unit")
tupleValue [x] = x
tupleValue (x : xs) = Application Explicit (Application Explicit (Variable (Identifier "pair")) x) (tupleValue xs)

checkIsType :: Context -> Expression -> Elab (Expression, Expression)
checkIsType context expression = case expression of
    Tuple [] -> synthesizeElab context (Variable (Identifier "Unit"))
    Tuple [x] -> checkIsType context x
    Tuple (x : xs) -> do
        (left, leftUniverse) <- checkIsType context x
        (right, rightUniverse) <- checkIsType context (Tuple xs)
        pure (Application Explicit (Application Explicit (Variable (Identifier "Pair")) left) right, maxUniverse leftUniverse rightUniverse)
    _ -> do
        (elab, universe) <- synthesizeElab context expression
        _ <- extractUniverseLevel context universe
        pure (elab, universe)
  where
    maxUniverse (Universe (UFixed a)) (Universe (UFixed b)) = Universe (UFixed (max a b))
    maxUniverse _ _ = Universe (UFixed (-1))

numericBinary :: Context -> Identifier -> Expression -> Expression -> Elab (Expression, Expression)
numericBinary context op left right = do
    (elabLeft, leftType0) <- synthesizeElab context left
    (elabRight, rightType0) <- synthesizeElab context right
    leftType <- zonk leftType0
    rightType <- zonk rightType0
    let boolType = Variable (Identifier "Bool")
    if op `elem` map Identifier ["==", "/="] && leftType == boolType && rightType == boolType
        then do
            let core = Application Explicit (Application Explicit (PrimOp BoolEq) elabLeft) elabRight
                result = if op == Identifier "/=" then Application Explicit (Variable (Identifier "not")) core else core
            pure (result, boolType)
        else if op == Identifier "++" && isListType leftType && isListType rightType
            then pure (Application Explicit (Application Explicit (Variable (Identifier "append")) elabLeft) elabRight, leftType)
            else numericBinaryRest elabLeft elabRight leftType rightType
  where
    isListType ty = case unfoldApp ty of
        (Variable (Identifier "List"), [_]) -> True
        _ -> False
    numericBinaryRest elabLeft elabRight leftType rightType = do
        let leftPrim = numericKind leftType
            rightPrim = numericKind rightType
            resultKind = case (leftPrim, rightPrim) of
                (Just PTFloat, _) -> Just PTFloat
                (_, Just PTFloat) -> Just PTFloat
                (Just PTInt, _) -> Just PTInt
                (_, Just PTInt) -> Just PTInt
                (Just PTChar, Just PTChar) -> Just PTChar
                _ -> Nothing
            comparison = op `elem` map Identifier ["==", "/=", "<", "<=", ">", ">="]
        case resultKind of
            Just kind ->
                case numericPrimitive op kind of
                    Just primitive -> do
                        let target = PrimType kind
                            l' = coerceNumeric kind elabLeft leftType
                            r' = coerceNumeric kind elabRight rightType
                            resultType = if comparison then Variable (Identifier "Bool") else target
                            (firstArg, secondArg) = if op `elem` map Identifier [">", ">="] then (r', l') else (l', r')
                            core = Application Explicit (Application Explicit (PrimOp primitive) firstArg) secondArg
                            result = if op == Identifier "/=" then Application Explicit (Variable (Identifier "not")) core else core
                        pure (result, resultType)
                    Nothing -> throwError (TypeMismatch (PrimType kind) leftType)
            _ -> throwError (TypeMismatch leftType rightType)

synthesizeElab :: Context -> Expression -> Elab (Expression, Expression)
synthesizeElab context expression = case expression of
    Located sp inner -> localSpan sp (synthesizeElab context inner)
    Variable identifier -> do
        rawType <- liftEither (lookupContext identifier context)
        instantiateLeadingImplicits context (Variable identifier) rawType
    Universe lvl -> do
        case lvl of
            UFixed n -> pure (Universe (UFixed n), Universe (UFixed (n + 1)))
            UVar u -> do
                u' <- freshUnivVar
                addUnivConstraint (ULt (UVar u) (UVar u'))
                pure (Universe (UVar u), Universe (UVar u'))
            UMax l1 l2 -> do
                u' <- freshUnivVar
                addUnivConstraint (ULt l1 (UVar u'))
                addUnivConstraint (ULt l2 (UVar u'))
                pure (Universe (UMax l1 l2), Universe (UVar u'))
            USucc l -> do
                u' <- freshUnivVar
                addUnivConstraint (ULt l (UVar u'))
                pure (Universe (USucc l), Universe (UVar u'))
    Identity -> pure (Identity, identityType)
    Reflexivity -> pure (Reflexivity, reflexivityType)
    J -> pure (J, jType)
    VoidType -> pure (VoidType, Universe (UFixed (-1)))
    Abort -> pure (Abort, abortType)
    Literal (LitInt n) -> pure (Literal (LitInt n), PrimType PTInt)
    Literal (LitFloat _) -> pure (expression, PrimType PTFloat)
    Literal (LitChar _) -> pure (expression, PrimType PTChar)
    Literal (LitString _) -> pure (expression, listCharType)
    Tuple [] -> synthesizeElab context (Variable (Identifier "unit"))
    Tuple elements -> synthesizeElab context (tupleValue elements)
    PrimType primitiveType -> pure (PrimType primitiveType, Universe (UFixed (-1)))
    PrimOp operation -> pure (expression, primitiveOpType operation)
    MetaVar i -> do
        substMap <- gets metaSubst
        case Map.lookup i substMap of
            Just term -> synthesizeElab context term
            Nothing -> do
                tMeta <- freshMeta context (Universe (UFixed (-1)))
                pure (MetaVar i, tMeta)
    Hole mName -> do
        tMeta <- freshMeta context (Universe (UFixed (-1)))
        mId <- freshMetaId
        recordMeta mId mName context tMeta
        pure (MetaVar mId, tMeta)
    Annotation term annotationType -> do
        (elabAnnType, annTypeUniverse) <- checkIsType context annotationType
        _ <- extractUniverseLevel context annTypeUniverse
        _ <- checkElab context term elabAnnType
        pure (term, elabAnnType)
    Let param maybeDeclaredType defExpr body -> do
        (elabDef, defType) <- case maybeDeclaredType of
            Just declaredType -> do
                (elabDeclType, typeUniverse) <- checkIsType context declaredType
                _ <- extractUniverseLevel context typeUniverse
                zonkedDeclType <- zonk elabDeclType
                elabVal <- checkElab context defExpr zonkedDeclType
                pure (elabVal, zonkedDeclType)
            Nothing -> do
                (elabVal, rawType) <- synthesizeElab context defExpr
                zonkedType <- zonk rawType
                pure (elabVal, zonkedType)
        zonkedDef <- zonk elabDef
        zonkedDefType <- zonk defType
        let extContext = extendContextDefinition param zonkedDefType zonkedDef context
            extContextWithLocal = extContext{contextLocals = param : contextLocals context}
        (elabBody, bodyType) <- synthesizeElab extContextWithLocal body
        zonkedBody <- zonk elabBody
        zonkedBodyType <- zonk bodyType
        let finalType = substitute param zonkedDef zonkedBodyType
        pure (Let param (Just zonkedDefType) zonkedDef zonkedBody, finalType)
    Case target mMotive branches -> do
        retMeta <- freshMeta context (Universe (UFixed (-1)))
        elabCase <- checkElab context (Case target mMotive branches) retMeta
        zonkedRet <- zonk retMeta
        pure (elabCase, zonkedRet)
    Projection expr field -> do
        (elabExpr, exprType) <- synthesizeElab context expr
        let (headExpr, _) = unfoldApp exprType
        case headExpr of
            Variable dataTypeName ->
                case Map.lookup dataTypeName (contextRecords context) of
                    Just _ | Map.member field (contextTypes context) -> do
                        (proj, _) <- instantiateLeadingImplicits context (Variable field) (fromMaybe (Universe (UFixed (-1))) (Map.lookup field (contextTypes context)))
                        pure (Application Explicit proj elabExpr, fromMaybe (Universe (UFixed (-1))) (Map.lookup field (contextTypes context)))
                    Just _ -> throwError (UnknownField field dataTypeName)
                    Nothing -> throwError (ExpectedDataType exprType)
            _ -> throwError (ExpectedDataType exprType)
    RecordLiteral recName fieldValues -> do
        recInfo <- case Map.lookup recName (contextRecords context) of
            Just info -> pure info
            Nothing -> throwError (UnboundVariable recName)
        let valueMap = Map.fromList fieldValues
        ordered <- traverse (\field ->
            case Map.lookup (recordFieldName field) valueMap of
                Just value -> pure value
                Nothing -> throwError (UnknownField (recordFieldName field) recName)) (recordFields recInfo)
        let constructor = Variable (recordConName recInfo)
            applied = foldl (Application Explicit) constructor ordered
        synthesizeElab context applied
    Application Explicit (Application Explicit (Variable op) left) right
        | numericOperator op -> numericBinary context op left right
    Pi vis parameter domain codomain -> do
        (elabDomain, domainUniverse) <- checkIsType context domain
        levelI <- extractUniverseLevel context domainUniverse
        let extendedContext = extendContextType parameter elabDomain context
        (elabCodomain, codomainUniverse) <- checkIsType extendedContext codomain
        levelJ <- extractUniverseLevel extendedContext codomainUniverse
        let maxLevel = if levelI == -1 || levelJ == -1 then -1 else max levelI levelJ
        pure (Pi vis parameter elabDomain elabCodomain, Universe (UFixed maxLevel))
    Application Explicit function argument -> do
        (fnExpr, functionType) <- synthesizeElab context function
        (instantiatedFn, fnType) <- instantiateLeadingImplicits context fnExpr functionType
        zonkedType <- zonk fnType
        let env = contextEnv context
        case evaluateWeakHeadNormalForm env zonkedType of
            Pi Explicit parameter domain codomain -> do
                elabArg <- checkElab context argument domain
                zonkedArg <- zonk elabArg
                pure (Application Explicit instantiatedFn zonkedArg, substitute parameter zonkedArg codomain)
            MetaVar i -> do
                paramDomain <- freshMeta context (Universe (UFixed (-1)))
                codomainMeta <- freshMeta context (Universe (UFixed (-1)))
                let assumedPi = Pi Explicit (Identifier "_") paramDomain codomainMeta
                solvePattern context i [] assumedPi
                elabArg <- checkElab context argument paramDomain
                zonkedArg <- zonk elabArg
                pure (Application Explicit instantiatedFn zonkedArg, substitute (Identifier "_") zonkedArg codomainMeta)
            nonFunctionType ->
                throwError (ExpectedFunctionType nonFunctionType)
    Application Implicit function argument -> do
        (fnExpr, functionType) <- synthesizeElab context function
        zonkedType <- zonk functionType
        let env = contextEnv context
        case evaluateWeakHeadNormalForm env zonkedType of
            Pi Implicit parameter domain codomain -> do
                elabArg <- checkElab context argument domain
                zonkedArg <- zonk elabArg
                pure (Application Implicit fnExpr zonkedArg, substitute parameter zonkedArg codomain)
            nonFunctionType ->
                throwError (ExpectedFunctionType nonFunctionType)
    Application Instance function argument -> do
        (fnExpr, functionType) <- synthesizeElab context function
        zonkedType <- zonk functionType
        let env = contextEnv context
        case evaluateWeakHeadNormalForm env zonkedType of
            Pi Instance parameter domain codomain -> do
                elabArg <- checkElab context argument domain
                zonkedArg <- zonk elabArg
                pure (Application Instance fnExpr zonkedArg, substitute parameter zonkedArg codomain)
            nonFunctionType ->
                throwError (ExpectedFunctionType nonFunctionType)
    Lambda vis parameter (Just parameterType) body -> do
        (elabParamType, paramUniverse) <- synthesizeElab context parameterType
        _ <- extractUniverseLevel context paramUniverse
        let extendedContext = extendContextType parameter elabParamType context
        (bodyExpr, bodyType) <- synthesizeElab extendedContext body
        (bodyTypeExpr, bodyUniverse) <- synthesizeElab extendedContext bodyType
        _ <- extractUniverseLevel extendedContext bodyUniverse
        pure (Lambda vis parameter (Just elabParamType) bodyExpr, Pi vis parameter elabParamType bodyTypeExpr)
    Lambda _ _ Nothing _ ->
        throwError (CannotSynthesizeType expression)

checkElab :: Context -> Expression -> Expression -> Elab Expression
checkElab context expression expType = case expression of
    -- Keep the term's source span installed until the complete check finishes.
    -- In particular, this must cover the final unify in the fallback below;
    -- synthesizeElab's own Located handler otherwise restores the enclosing
    -- definition span before that unify can report an error.
    Located sp inner -> do
        previous <- gets activeSpan
        modify (\s -> s{activeSpan = Just sp})
        result <- checkElab context inner expType
        modify (\s -> s{activeSpan = previous})
        pure result
    _ -> do
        zonkedExpected <- zonk expType
        let env = contextEnv context
            whnfExpected = evaluateWeakHeadNormalForm env zonkedExpected
        case (expression, whnfExpected) of
            (Tuple [], _) -> checkElab context (Variable (Identifier "unit")) whnfExpected
            (Tuple elements, Universe _) -> fst <$> checkIsType context (Tuple elements)
            (Tuple elements, _) -> checkElab context (tupleValue elements) whnfExpected
            (Literal (LitInt n), PrimType PTInt) -> pure (Literal (LitInt n))
            (Literal (LitInt n), PrimType PTFloat) -> pure (Literal (LitFloat (fromIntegral n)))
            (Literal (LitFloat n), PrimType PTFloat) -> pure (Literal (LitFloat n))
            (Literal (LitChar c), PrimType PTChar) -> pure (Literal (LitChar c))
            (Literal (LitString s), ty) | ty == listCharType -> pure (Literal (LitString s))
            (Hole mName, _) -> do
                mId <- freshMetaId
                recordMeta mId mName context zonkedExpected
                pure (MetaVar mId)
            (Case target mMotive branches, _) -> do
                (elabTarget, rawTargetType) <- synthesizeElab context target
                zonkedTargetType <- zonk rawTargetType
                let whnfTargetType = evaluateWeakHeadNormalForm env zonkedTargetType
                elabBranches <- checkCaseBranches checkElab context elabTarget whnfTargetType whnfExpected mMotive branches
                pure (Case elabTarget mMotive elabBranches)
            (Let param maybeDeclaredType defExpr body, _) -> do
                (elabDef, defType) <- case maybeDeclaredType of
                    Just declaredType -> do
                        (elabDeclType, typeUniverse) <- checkIsType context declaredType
                        _ <- extractUniverseLevel context typeUniverse
                        zonkedDeclType <- zonk elabDeclType
                        elabVal <- checkElab context defExpr zonkedDeclType
                        pure (elabVal, zonkedDeclType)
                    Nothing -> do
                        (elabVal, rawType) <- synthesizeElab context defExpr
                        zonkedType <- zonk rawType
                        pure (elabVal, zonkedType)
                zonkedDef <- zonk elabDef
                zonkedDefType <- zonk defType
                let extContext = extendContextDefinition param zonkedDefType zonkedDef context
                    extContextWithLocal = extContext{contextLocals = param : contextLocals context}
                elabBody <- checkElab extContextWithLocal body whnfExpected
                zonkedBody <- zonk elabBody
                pure (Let param (Just zonkedDefType) zonkedDef zonkedBody)
            (Lambda Explicit parameter maybeDeclaredType body, Pi Explicit binder domain codomain) -> do
                case maybeDeclaredType of
                    Just declaredType -> do
                        (elabDeclType, declUniverse) <- synthesizeElab context declaredType
                        _ <- extractUniverseLevel context declUniverse
                        unify context elabDeclType domain
                    Nothing -> pure ()
                let targetParameter = parameter
                    substitutedCodomain = substitute binder (Variable targetParameter) codomain
                    extendedContext = extendContextType targetParameter domain context
                elaboratedBody <- checkElab extendedContext body substitutedCodomain
                pure (Lambda Explicit targetParameter (Just domain) elaboratedBody)
            (Lambda Implicit parameter maybeDeclaredType body, Pi Implicit binder domain codomain) -> do
                case maybeDeclaredType of
                    Just declaredType -> do
                        (elabDeclType, declUniverse) <- synthesizeElab context declaredType
                        _ <- extractUniverseLevel context declUniverse
                        unify context elabDeclType domain
                    Nothing -> pure ()
                let targetParameter = parameter
                    substitutedCodomain = substitute binder (Variable targetParameter) codomain
                    extendedContext = extendContextType targetParameter domain context
                elaboratedBody <- checkElab extendedContext body substitutedCodomain
                pure (Lambda Implicit targetParameter (Just domain) elaboratedBody)
            (Lambda Instance parameter maybeDeclaredType body, Pi Instance binder domain codomain) -> do
                case maybeDeclaredType of
                    Just declaredType -> do
                        (elabDeclType, declUniverse) <- synthesizeElab context declaredType
                        _ <- extractUniverseLevel context declUniverse
                        unify context elabDeclType domain
                    Nothing -> pure ()
                let targetParameter = parameter
                    substitutedCodomain = substitute binder (Variable targetParameter) codomain
                    extendedContext =
                        (extendContextType targetParameter domain context)
                            { contextLocals = targetParameter : contextLocals context
                            }
                elaboratedBody <- checkElab extendedContext body substitutedCodomain
                pure (Lambda Instance targetParameter (Just domain) elaboratedBody)
            (Lambda Explicit parameter maybeDeclaredType body, MetaVar i) -> do
                dom <- case maybeDeclaredType of
                    Just declType -> do
                        (elabDeclType, _) <- synthesizeElab context declType
                        zonk elabDeclType
                    Nothing -> freshMeta context (Universe (UFixed (-1)))
                codom <- freshMeta (extendContextType parameter dom context) (Universe (UFixed (-1)))
                solvePattern context i [] (Pi Explicit parameter dom codom)
                checkElab context (Lambda Explicit parameter maybeDeclaredType body) (Pi Explicit parameter dom codom)
            (Lambda Implicit parameter maybeDeclaredType body, MetaVar i) -> do
                dom <- case maybeDeclaredType of
                    Just declType -> do
                        (elabDeclType, _) <- synthesizeElab context declType
                        zonk elabDeclType
                    Nothing -> freshMeta context (Universe (UFixed (-1)))
                codom <- freshMeta (extendContextType parameter dom context) (Universe (UFixed (-1)))
                solvePattern context i [] (Pi Implicit parameter dom codom)
                checkElab context (Lambda Implicit parameter maybeDeclaredType body) (Pi Implicit parameter dom codom)
            (otherExpr, Pi Implicit binder domain codomain) -> do
                let extendedContext = extendContextType binder domain context
                elaboratedBody <- checkElab extendedContext otherExpr codomain
                pure (Lambda Implicit binder (Just domain) elaboratedBody)
            (otherExpr, Pi Instance binder domain codomain) -> do
                let extendedContext =
                        (extendContextType binder domain context)
                            { contextLocals = binder : contextLocals context
                            }
                elaboratedBody <- checkElab extendedContext otherExpr codomain
                pure (Lambda Instance binder (Just domain) elaboratedBody)
            (Lambda _ _ _ _, notPiType) ->
                throwError (ExpectedFunctionType notPiType)
            (otherExpression, _) -> do
                (elabExpr, synthesizedType) <- synthesizeElab context otherExpression
                let actual = evaluateWeakHeadNormalForm env synthesizedType
                    expected = evaluateWeakHeadNormalForm env zonkedExpected
                    coerced = case (actual, expected) of
                        (PrimType PTInt, PrimType PTFloat) -> Just (Application Explicit (PrimOp IntToFloat) elabExpr)
                        _ -> Nothing
                case coerced of
                    Just term -> pure term
                    Nothing -> unify context synthesizedType zonkedExpected >> pure elabExpr
