{-# LANGUAGE OverloadedStrings #-}

module TypeChecker (
    TypeError (..),
    TypeDiagnostic (..),
    Goal (..),
    Context (..),
    DataInfo (..),
    emptyContext,
    extendContextType,
    extendContextDefinition,
    checkDataDeclaration,
    checkRecordDeclaration,
    checkClassDeclaration,
    checkClassDeclarationDetailed,
    checkInstanceDeclaration,
    checkInstanceDeclarationDetailed,
    synthesize,
    check,
    checkDefinition,
    checkDefinitionWithPartial,
    checkFunctionDefinition,
    checkFunctionDefinitionWithPartial,
    lookupContext,
    renderTypeError,
    renderTypeDiagnostic,
    renderGoals,
) where

import AST (CaseBranch (..), ClassMethod (..), Clause (..), Expression (..), Fixity (..), Identifier (..), Literal (..), Pattern (..), PrimOp (..), PrimType (..), RecordField (..), RecordInfo (..), UniverseLevel (..), Visibility (..))
import Control.Monad (filterM, foldM, unless)
import Control.Monad.State.Strict (StateT (..), evalStateT, gets, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Char (isLower)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import Diagnostics (SourceSpan (..), formatSourceSnippet)
import Parser (defaultFixityEnv)
import Evaluation (Environment, Value (..), areDefinitionallyEqual, emptyEnvironment, evaluate, evaluateWeakHeadNormalForm)
import Pretty (prettyExpression, prettyIdentifier)
import Substitution (freeVariables, freshIdentifier, substitute)
import PatternMatch (compileClauses)

data Goal = Goal
    { goalId :: !Int
    , goalName :: !(Maybe Identifier)
    , goalExpected :: !Expression
    , goalLocals :: ![(Identifier, Expression)]
    }
    deriving (Eq, Show)

data MetaInfo = MetaInfo
    { metaInfoName :: !(Maybe Identifier)
    , metaInfoExpected :: !Expression
    , metaInfoContext :: !Context
    }
    deriving (Eq, Show)

data DataInfo = DataInfo
    { dataParams :: ![(Visibility, Identifier, Expression)]
    , dataIndices :: ![(Visibility, Identifier, Expression)]
    , dataUniverse :: !Expression
    , dataConstructors :: ![(Identifier, Expression)]
    }
    deriving (Eq, Show)

data TypeError
    = UnboundVariable Identifier
    | TypeMismatch
        { expectedType :: Expression
        , actualType :: Expression
        }
    | ExpectedFunctionType
        { actualType :: Expression
        }
    | ExpectedUniverse
        { actualType :: Expression
        }
    | CannotSynthesizeType Expression
    | CannotMatchOnNonDataType Expression
    | ExpectedDataType Expression
    | UnknownField Identifier Identifier
    | NoInstanceFound Expression
    | AmbiguousInstance Expression [Identifier]
    | NonExhaustivePatternMatch Identifier [Identifier]
    | UnknownConstructor Identifier Identifier
    | ArityMismatch Identifier Int Int
    | OccursCheckFailed Int Expression
    | ScopeEscapeFailed Int Identifier Expression
    | NonStrictlyPositive Identifier Identifier
    | NonTerminatingDefinition Identifier
    | UnsolvedMetavariable Int
    | UniverseInconsistency Text
    deriving (Eq, Show)

-- | Universe level constraints.
data UnivConstraint
    = ULeq UniverseLevel UniverseLevel  -- l1 <= l2
    | ULt UniverseLevel UniverseLevel   -- l1 < l2  (i.e., l1 + 1 <= l2)
    deriving (Eq, Show)

data TypeDiagnostic = TypeDiagnostic
    { diagSpan  :: !(Maybe SourceSpan)
    , diagTrace :: ![Text]
    , diagError :: !TypeError
    } deriving (Eq, Show)

data Context = Context
    { contextTypes :: Map Identifier Expression
    , contextValues :: Map Identifier Expression
    , contextEnv :: Environment
    , contextLocals :: [Identifier]
    , contextData :: Map Identifier DataInfo
    , contextFixities :: Map Identifier Fixity
    , contextRecords :: Map Identifier RecordInfo
    , contextInstances :: Map Identifier [Identifier]
    , contextClassDefaults :: Map Identifier [(Identifier, Expression)]
    }
    deriving (Eq, Show)

builtinData :: Map Identifier DataInfo
builtinData =
    Map.fromList
        [
            ( Identifier "Nat"
            , DataInfo
                { dataParams = []
                , dataIndices = []
                , dataUniverse = Universe (UFixed (-1))
                , dataConstructors =
                    [ (Identifier "zero", NatType)
                    , (Identifier "successor", Pi Explicit (Identifier "_") NatType NatType)
                    ]
                }
            )
        ,
            ( Identifier "Void"
            , DataInfo
                { dataParams = []
                , dataIndices = []
                , dataUniverse = Universe (UFixed (-1))
                , dataConstructors = []
                }
            )
        ]

emptyContext :: Context
emptyContext =
    Context
        { contextTypes =
            Map.union primitiveTypes (Map.fromList
                [ (Identifier "zero", NatType)
                , (Identifier "successor", Pi Explicit (Identifier "_") NatType NatType)
                ])
        , contextValues =
            Map.union primitiveValues (Map.fromList
                [ (Identifier "zero", Zero)
                , (Identifier "successor", Succ)
                ])
        , contextEnv =
            Map.union (Map.map (evaluate emptyEnvironment) primitiveValues)
                (Map.fromList
                    [ (Identifier "zero", VZero)
                    , (Identifier "successor", VPrimSucc)
                    ])
        , contextLocals = []
        , contextData = builtinData
        , contextFixities = defaultFixityEnv
        , contextRecords = Map.empty
        , contextInstances = Map.empty
        , contextClassDefaults = Map.empty
        }

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

extendContextType :: Identifier -> Expression -> Context -> Context
extendContextType identifier expressionType context =
    context
        { contextTypes = Map.insert identifier expressionType (contextTypes context)
        , contextEnv = Map.delete identifier (contextEnv context)
        , contextLocals = identifier : contextLocals context
        }

extendContextDefinition :: Identifier -> Expression -> Expression -> Context -> Context
extendContextDefinition identifier expressionType expressionValue context =
    let oldEnv = contextEnv context
        value = if isFunctionExpression expressionValue
            then evaluate recursiveEnv expressionValue
            else evaluate oldEnv expressionValue
        recursiveEnv = Map.insert identifier (evaluate recursiveEnv expressionValue) oldEnv
     in context
            { contextTypes = Map.insert identifier expressionType (contextTypes context)
            , contextValues = Map.insert identifier expressionValue (contextValues context)
            , contextEnv = Map.insert identifier value (contextEnv context)
            }

-- Recursive definitions are represented by closures whose environment contains
-- their own binding.  Restricting this knot to lambdas is important: a bare
-- value redefinition such as `a = successor a` must read the old environment,
-- not recursively force itself.
isFunctionExpression :: Expression -> Bool
isFunctionExpression expression = case expression of
    Located _ inner -> isFunctionExpression inner
    Annotation inner _ -> isFunctionExpression inner
    Lambda _ _ _ _ -> True
    _ -> False

lookupContext :: Identifier -> Context -> Either TypeError Expression
lookupContext identifier context =
    case Map.lookup identifier (contextTypes context) of
        Just expressionType -> pure expressionType
        Nothing -> Left (UnboundVariable identifier)

data ElabState = ElabState
    { nextMetaId :: !Int
    , metaSubst :: !(Map Int Expression)
    , metaRegistry :: !(Map Int MetaInfo)
    , activeSpan :: !(Maybe SourceSpan)
    , elabTrace  :: ![Text]
    , nextUnivVar :: !Int
    , univConstraints :: ![UnivConstraint]
    }

type Elab a = StateT ElabState (Either TypeDiagnostic) a

throwError :: TypeError -> Elab a
throwError err = do
    sp <- gets activeSpan
    trace <- gets elabTrace
    lift $ Left (TypeDiagnostic sp trace err)

liftEither :: Either TypeError a -> Elab a
liftEither (Left err) = throwError err
liftEither (Right val) = pure val

localSpan :: SourceSpan -> Elab a -> Elab a
localSpan sp action = do
    prev <- gets activeSpan
    modify (\s -> s{activeSpan = Just sp})
    result <- action
    modify (\s -> s{activeSpan = prev})
    pure result

localTrace :: Text -> Elab a -> Elab a
localTrace msg action = do
    prev <- gets elabTrace
    modify (\s -> s{elabTrace = msg : prev})
    result <- action
    modify (\s -> s{elabTrace = prev})
    pure result

catchElab :: Elab a -> (TypeDiagnostic -> Elab a) -> Elab a
catchElab (StateT action) handler = StateT $ \s ->
    case action s of
        Left diag -> runStateT (handler diag) s
        Right (res, s') -> Right (res, s')

tryElab :: Elab a -> Elab a -> Elab a
tryElab primary fallback = catchElab primary (\_ -> fallback)

freshMetaId :: Elab Int
freshMetaId = do
    idx <- gets nextMetaId
    modify (\s -> s{nextMetaId = idx + 1})
    pure idx

freshUnivVar :: Elab Int
freshUnivVar = do
    idx <- gets nextUnivVar
    modify (\s -> s{nextUnivVar = idx + 1})
    pure idx

addUnivConstraint :: UnivConstraint -> Elab ()
addUnivConstraint c = modify (\s -> s{univConstraints = c : univConstraints s})

freshMeta :: Context -> Expression -> Elab Expression
freshMeta ctx expType = do
    mId <- freshMetaId
    recordMeta mId Nothing ctx expType
    pure (MetaVar mId)

recordMeta :: Int -> Maybe Identifier -> Context -> Expression -> Elab ()
recordMeta mId mName context expType = do
    let info = MetaInfo mName expType context
    modify (\s -> s{metaRegistry = Map.insert mId info (metaRegistry s)})

collectUnsolvedGoals :: Elab [Goal]
collectUnsolvedGoals = do
    registry <- gets metaRegistry
    substMap <- gets metaSubst
    let unsolved = Map.filterWithKey (\mId _ -> Map.notMember mId substMap) registry
    traverse toGoal (Map.toList unsolved)
  where
    toGoal (mId, info) = do
        zonkedExp <- zonk (metaInfoExpected info)
        let ctx = metaInfoContext info
            env = contextEnv ctx
            normExp = evaluateWeakHeadNormalForm env zonkedExp
        locals <- traverse (zonkLocal ctx) (contextLocals ctx)
        pure
            Goal
                { goalId = mId
                , goalName = metaInfoName info
                , goalExpected = normExp
                , goalLocals = locals
                }

    zonkLocal ctx ident = do
        let rawType = Map.findWithDefault (Universe (UFixed (-1))) ident (contextTypes ctx)
        zonkedType <- zonk rawType
        let normType = evaluateWeakHeadNormalForm (contextEnv ctx) zonkedType
        pure (ident, normType)

zonk :: Expression -> Elab Expression
zonk expr = do
    substMap <- gets metaSubst
    case expr of
        MetaVar i ->
            case Map.lookup i substMap of
                Just resolved -> zonk resolved
                Nothing -> pure (MetaVar i)
        Application vis f a -> Application vis <$> zonk f <*> zonk a
        Lambda vis p ty body -> Lambda vis p <$> traverse zonk ty <*> zonk body
        Pi vis p d c -> Pi vis p <$> zonk d <*> zonk c
        Let p ty d b -> Let p <$> traverse zonk ty <*> zonk d <*> zonk b
        Case target mMotive branches ->
            Case <$> zonk target <*> traverse zonkMotive mMotive <*> traverse zonkBranch branches
          where
            zonkMotive (mv, mt) = (,) mv <$> zonk mt
            zonkBranch (CaseBranch pat body) = CaseBranch pat <$> zonk body
        Annotation t ty -> Annotation <$> zonk t <*> zonk ty
        Located sp e -> Located sp <$> zonk e
        other -> pure other

occursIn :: Int -> Expression -> Bool
occursIn i expr = case expr of
    MetaVar j -> i == j
    Application _ f a -> occursIn i f || occursIn i a
    Lambda _ _ ty body -> maybe False (occursIn i) ty || occursIn i body
    Pi _ _ d c -> occursIn i d || occursIn i c
    Let _ ty d b -> maybe False (occursIn i) ty || occursIn i d || occursIn i b
    Case target mMotive branches ->
        occursIn i target || any (\(CaseBranch _ b) -> occursIn i b) branches || case mMotive of
            Just (_, mt) -> occursIn i mt
            Nothing -> False
    Annotation t ty -> occursIn i t || occursIn i ty
    Located _ e -> occursIn i e
    _ -> False

unfoldApp :: Expression -> (Expression, [(Visibility, Expression)])
unfoldApp expression = collect expression []
  where
    collect (Application vis fn arg) args = collect (stripLocated fn) ((vis, arg) : args)
    collect headExpr args = (stripLocated headExpr, args)

stripLocated :: Expression -> Expression
stripLocated (Located _ e) = stripLocated e
stripLocated e = e

checkPatternSpine :: [(Visibility, Expression)] -> Maybe [(Visibility, Identifier)]
checkPatternSpine = traverse extractVar
  where
    extractVar (vis, Variable ident) = Just (vis, ident)
    extractVar _ = Nothing

isLinear :: [(Visibility, Identifier)] -> Bool
isLinear vars =
    let idents = map snd vars
     in Set.size (Set.fromList idents) == length idents

solvePattern :: Context -> Int -> [(Visibility, Identifier)] -> Expression -> Elab ()
solvePattern ctx mId spine rhs = do
    zonkedRhs <- zonk rhs
    if occursIn mId zonkedRhs
        then throwError (OccursCheckFailed mId zonkedRhs)
        else do
            reg <- gets metaRegistry
            let allowedVars = case Map.lookup mId reg of
                    Just info -> Map.keysSet (contextTypes (metaInfoContext info))
                    Nothing -> Map.keysSet (contextTypes ctx)
                spineVarSet = Set.fromList (map snd spine)
                validVars = Set.union allowedVars spineVarSet
                rhsFreeVars = freeVariables zonkedRhs
                escapingVars = Set.difference rhsFreeVars validVars
            case Set.lookupMin escapingVars of
                Just escaped ->
                    throwError (ScopeEscapeFailed mId escaped zonkedRhs)
                Nothing -> do
                    let solution = foldr (\(vis, param) body -> Lambda vis param Nothing body) zonkedRhs spine
                    modify (\s -> s{metaSubst = Map.insert mId solution (metaSubst s)})

extractUniverseLevel :: Context -> Expression -> Elab Int
extractUniverseLevel context expr = do
    z <- zonk expr
    let env = contextEnv context
        w = evaluateWeakHeadNormalForm env z
    case w of
        Universe lvl -> pure (levelToInt lvl)
        MetaVar i -> do
            solvePattern context i [] (Universe (UFixed (-1)))
            pure (-1)
        other -> throwError (ExpectedUniverse other)
  where
    levelToInt (UFixed n) = n
    levelToInt (UVar _) = -1
    levelToInt (UMax l1 l2) = max (levelToInt l1) (levelToInt l2)
    levelToInt (USucc l) = levelToInt l + 1

unify :: Context -> Expression -> Expression -> Elab ()
unify ctx e1 e2 = do
    z1 <- zonk (stripLocated e1)
    z2 <- zonk (stripLocated e2)
    let (h1, sp1) = unfoldApp z1
        (h2, sp2) = unfoldApp z2
    case (h1, sp1, h2, sp2) of
        (MetaVar i, [], MetaVar j, [])
            | i == j -> pure ()
            | otherwise -> do
                reg <- gets metaRegistry
                case (Map.lookup i reg, Map.lookup j reg) of
                    (Just infoI, Just infoJ) ->
                        let varsI = Map.keysSet (contextTypes (metaInfoContext infoI))
                            varsJ = Map.keysSet (contextTypes (metaInfoContext infoJ))
                         in if Set.isSubsetOf varsI varsJ
                                then solvePattern ctx j [] (MetaVar i)
                                else solvePattern ctx i [] (MetaVar j)
                    _ -> solvePattern ctx i [] (MetaVar j)
        (MetaVar i, _, MetaVar j, _)
            | i == j && sp1 == sp2 -> pure ()
        (MetaVar i, _, _, _)
            | Just spineVars <- checkPatternSpine sp1
            , isLinear spineVars ->
                tryElab (solvePattern ctx i spineVars z2) (unfoldAndRetry z1 z2)
        (_, _, MetaVar j, _)
            | Just spineVars <- checkPatternSpine sp2
            , isLinear spineVars ->
                tryElab (solvePattern ctx j spineVars z1) (unfoldAndRetry z1 z2)
        (Universe l1, [], Universe l2, []) -> do
            addUnivConstraint (ULeq l1 l2)
            pure ()
        _ -> case (z1, z2) of
            (Application v1 f1 a1, Application v2 f2 a2)
                | v1 == v2 ->
                    tryElab
                        ( do
                            unify ctx f1 f2
                            unify ctx a1 a2
                        )
                        (unfoldAndRetry z1 z2)
            (Pi v1 p1 d1 c1, Pi v2 p2 d2 c2)
                | v1 == v2 ->
                    tryElab
                        ( do
                            unify ctx d1 d2
                            if p1 == p2
                                then unify (extendContextType p1 d1 ctx) c1 c2
                                else do
                                    let fresh = freshIdentifier p1 (Set.union (freeVariables c1) (freeVariables c2))
                                        extCtx = extendContextType fresh d1 ctx
                                    unify extCtx (substitute p1 (Variable fresh) c1) (substitute p2 (Variable fresh) c2)
                        )
                        (unfoldAndRetry z1 z2)
            (Identity, Identity) -> pure ()
            (Reflexivity, Reflexivity) -> pure ()
            (J, J) -> pure ()
            (VoidType, VoidType) -> pure ()
            (Abort, Abort) -> pure ()
            (NatType, NatType) -> pure ()
            (Zero, Zero) -> pure ()
            (Succ, Succ) -> pure ()
            (NatRec, NatRec) -> pure ()
            (Variable x, Variable y) | x == y -> pure ()
            _ -> unfoldAndRetry z1 z2
  where
    unfoldAndRetry :: Expression -> Expression -> Elab ()
    unfoldAndRetry t1 t2 = do
        let env = contextEnv ctx
            w1 = evaluateWeakHeadNormalForm env t1
            w2 = evaluateWeakHeadNormalForm env t2
            (wh1, wsp1) = unfoldApp w1
            (wh2, wsp2) = unfoldApp w2
            fallbackDefEq =
                if w1 /= t1 || w2 /= t2
                    then unify ctx w1 w2
                    else
                        if areDefinitionallyEqual env w1 w2
                            then pure ()
                            else throwError (TypeMismatch t2 t1)
        case (wh1, wsp1, wh2, wsp2) of
            (MetaVar i, _, _, _)
                | Just spineVars <- checkPatternSpine wsp1
                , isLinear spineVars ->
                    tryElab (solvePattern ctx i spineVars w2) fallbackDefEq
            (_, _, MetaVar j, _)
                | Just spineVars <- checkPatternSpine wsp2
                , isLinear spineVars ->
                    tryElab (solvePattern ctx j spineVars w1) fallbackDefEq
            (Universe l1, [], Universe l2, []) -> do
                addUnivConstraint (ULeq l1 l2)
                pure ()
            _ -> fallbackDefEq

-- | Solve universe level constraints. Collects all constraints from the
-- elaboration state, flattens UMax/USucc into difference constraints, and
-- checks for inconsistencies (e.g., Type : Type would create 0 <= -1).
solveUnivConstraints :: Elab ()
solveUnivConstraints = do
    constraints <- gets univConstraints
    case checkConstraints constraints of
        Left msg -> throwError (UniverseInconsistency msg)
        Right () -> pure ()

-- | Check a list of universe constraints. Returns Left with an error message
-- if any constraint is violated.
checkConstraints :: [UnivConstraint] -> Either Text ()
checkConstraints = foldM checkConstraint ()
  where
    checkConstraint () (ULeq l1 l2) = checkLeq l1 l2 0
    checkConstraint () (ULt l1 l2) = checkLeq l1 l2 (-1)

    -- | Check l1 <= l2 + c.
    checkLeq l1 l2 c = case levelValue l1 of
        Just v1 -> case levelValue l2 of
            Just v2 ->
                if v1 <= v2 + c
                    then Right ()
                    else Left
                        ( "Universe level inconsistency: "
                            <> prettyUnivLevel l1
                            <> " <= "
                            <> prettyUnivLevel l2
                            <> " + "
                            <> Text.pack (show c)
                        )
            Nothing -> Right ()  -- Can't fully check l2 yet; assume OK
        Nothing -> Right ()  -- Can't fully check l1 yet; assume OK

    -- | Compute the integer value of a universe level, if fully determined.
    levelValue :: UniverseLevel -> Maybe Int
    levelValue (UFixed n) = Just n
    levelValue (UVar _) = Nothing
    levelValue (UMax l1 l2) = max <$> levelValue l1 <*> levelValue l2
    levelValue (USucc l) = (+1) <$> levelValue l

    -- | Pretty-print a universe level for error messages.
    prettyUnivLevel :: UniverseLevel -> Text
    prettyUnivLevel (UFixed n) = Text.pack (show n)
    prettyUnivLevel (UVar u) = "?u" <> Text.pack (show u)
    prettyUnivLevel (UMax l1 l2) = "max(" <> prettyUnivLevel l1 <> "," <> prettyUnivLevel l2 <> ")"
    prettyUnivLevel (USucc l) = "succ(" <> prettyUnivLevel l <> ")"

instantiateLeadingImplicits :: Context -> Expression -> Expression -> Elab (Expression, Expression)
instantiateLeadingImplicits context expr exprType = do
    zonkedType <- zonk exprType
    let env = contextEnv context
        whnfType = evaluateWeakHeadNormalForm env zonkedType
    case whnfType of
        Pi Implicit param domain codomain -> do
            meta <- freshMeta context domain
            let newExpr = Application Implicit expr meta
                newType = substitute param meta codomain
            instantiateLeadingImplicits context newExpr newType
        Pi Instance param domain codomain -> do
            instanceExpr <- resolveInstance context domain
            let newExpr = Application Instance expr instanceExpr
                newType = substitute param instanceExpr codomain
            instantiateLeadingImplicits context newExpr newType
        _ ->
            pure (expr, zonkedType)

resolveInstance :: Context -> Expression -> Elab Expression
resolveInstance context domain = do
    let (headExpr, _) = unfoldApp domain
        className = case headExpr of
            Variable name -> Just name
            _ -> Nothing
        localCandidates =
            [ name
            | name <- contextLocals context
            , Just ty <- [Map.lookup name (contextTypes context)]
            , areDefinitionallyEqual (contextEnv context) ty domain
            ]
        registeredCandidates = case className of
            Nothing -> []
            Just name ->
                [ instanceName
                | instanceName <- Map.findWithDefault [] name (contextInstances context)
                , Just ty <- [Map.lookup instanceName (contextTypes context)]
                , areDefinitionallyEqual (contextEnv context) ty domain
                ]
        candidates = Set.toList (Set.fromList (localCandidates ++ registeredCandidates))
    case candidates of
        [name] -> pure (Variable name)
        [] -> throwError (NoInstanceFound domain)
        names -> throwError (AmbiguousInstance domain names)

identityType, reflexivityType, jType, abortType, succType, natRecType :: Expression
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
succType =
    Pi Explicit (Identifier "_") NatType NatType
natRecType =
    Pi Explicit (Identifier "P") pType
        $ Pi Explicit (Identifier "z") zType
        $ Pi Explicit (Identifier "s") sType
        $ Pi Explicit (Identifier "n") NatType codomainType
  where
    pType = Pi Explicit (Identifier "_") NatType (Universe (UFixed (-1)))
    zType = Application Explicit (Variable (Identifier "P")) Zero
    nVar = Variable (Identifier "n")
    pn = Application Explicit (Variable (Identifier "P")) nVar
    psuccn = Application Explicit (Variable (Identifier "P")) (Application Explicit Succ nVar)
    sType = Pi Explicit (Identifier "n") NatType (Pi Explicit (Identifier "_") pn psuccn)
    codomainType = Application Explicit (Variable (Identifier "P")) nVar

checkCaseBranches ::
    Context ->
    Expression ->
    Expression ->
    Expression ->
    Maybe (Identifier, Expression) ->
    [CaseBranch] ->
    Elab [CaseBranch]
checkCaseBranches context elabTarget whnfTargetType expType mMotive branches = do
    case whnfTargetType of
        PrimType pt -> checkPrimitiveCaseBranches context pt expType branches
        _ -> checkDataCaseBranches context elabTarget whnfTargetType expType mMotive branches

checkPrimitiveCaseBranches :: Context -> PrimType -> Expression -> [CaseBranch] -> Elab [CaseBranch]
checkPrimitiveCaseBranches context pt expType branches = do
    let defaultSeen = any (\(CaseBranch pat _) -> case pat of { PatWild -> True; PatVar _ -> True; PatCon _ [] -> True; _ -> False }) branches
    if not defaultSeen
        then throwError (NonExhaustivePatternMatch (Identifier (Text.pack (show pt))) [Identifier "_"])
        else traverse checkOne branches
  where
    checkOne branch@(CaseBranch pat body) = do
        let (effectivePat, branchContext) = case pat of
                PatCon n [] -> (PatVar n, extendContextType n (PrimType pt) context)
                PatVar n -> (PatVar n, extendContextType n (PrimType pt) context)
                PatWild -> (PatWild, context)
                PatLit (LitNat n) | pt == PTInt -> (PatLit (LitInt n), context)
                PatLit (LitNat n) | pt == PTFloat -> (PatLit (LitFloat (fromIntegral n)), context)
                PatLit lit -> (PatLit lit, context)
                _ -> (pat, context)
        case effectivePat of
            PatLit lit | literalPrimType lit /= Just pt -> throwError (TypeMismatch (PrimType pt) (literalType lit))
            PatCon _ _ -> throwError (CannotMatchOnNonDataType (PrimType pt))
            _ -> pure ()
        CaseBranch effectivePat <$> checkElab branchContext body expType
    literalType (LitNat _) = NatType
    literalType (LitInt _) = PrimType PTInt
    literalType (LitFloat _) = PrimType PTFloat
    literalType (LitChar _) = PrimType PTChar
    literalType (LitString _) = PrimType PTString
    literalPrimType (LitNat _) = Just PTInt
    literalPrimType (LitInt _) = Just PTInt
    literalPrimType (LitFloat _) = Just PTFloat
    literalPrimType (LitChar _) = Just PTChar
    literalPrimType (LitString _) = Just PTString

checkDataCaseBranches context elabTarget whnfTargetType expType mMotive branches = do
    let (headExpr, typeArgs) = unfoldApp whnfTargetType
    dataTypeName <- case headExpr of
        Variable ident -> pure ident
        NatType -> pure (Identifier "Nat")
        VoidType -> pure (Identifier "Void")
        other -> throwError (CannotMatchOnNonDataType other)
    dataInfo <- case Map.lookup dataTypeName (contextData context) of
        Just info -> pure info
        Nothing -> throwError (CannotMatchOnNonDataType headExpr)
    let numParams = length (dataParams dataInfo)
        (paramArgs, indexArgs) = splitAt numParams typeArgs
        paramArgsExprs = map snd paramArgs
        indexArgsExprs = map snd indexArgs
        expectedConstructors = map fst (dataConstructors dataInfo)
    -- Determine which expected constructors are non-absurd (can unify with
    -- target indices). Only non-absurd constructors are required for
    -- exhaustiveness; absurd branches (e.g. vnil against Vec A (succ k)) are
    -- unreachable and need not be covered.
    expectedNonAbsurd <-
        filterM
            ( \cName ->
                isConNonAbsurd
                    context
                    dataInfo
                    paramArgsExprs
                    indexArgsExprs
                    dataTypeName
                    cName
            )
            expectedConstructors
    let branchConstructors = [c | CaseBranch (PatCon c _) _ <- branches]
        hasDefault = any (\(CaseBranch p _) -> case p of { PatWild -> True; PatVar _ -> True; _ -> False }) branches
        missingConstructors =
            filter (`notElem` branchConstructors) expectedNonAbsurd
    if not hasDefault && not (null missingConstructors) && dataTypeName /= Identifier "Void"
        then throwError (NonExhaustivePatternMatch dataTypeName missingConstructors)
        else traverse
            ( checkBranch
                context
                elabTarget
                dataInfo
                paramArgsExprs
                indexArgsExprs
                dataTypeName
                whnfTargetType
                mMotive
                expType
            )
            branches

-- | Check whether a case branch's constructor indices unify with the target's
-- indices. If they don't (e.g. `vnil` against `Vec A (successor k)`), the branch
-- is absurd/unreachable and does not count for exhaustiveness.
isConNonAbsurd ::
    Context ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Identifier ->
    Elab Bool
isConNonAbsurd context dataInfo paramArgs indexArgs dataTypeName cName = do
    localConType <-
        case lookup cName (dataConstructors dataInfo) of
            Just ty -> pure ty
            Nothing -> throwError (UnknownConstructor dataTypeName cName)
    conIndexArgs <- extractConIndexArgs context localConType paramArgs dataTypeName
    case conIndexArgs of
        Just cargs -> do
            result <-
                catchElab
                    ( unifyIndexArgs context cargs indexArgs >> pure True
                    )
                    (const (pure False))
            pure result
        Nothing -> pure (False :: Bool)

-- | Extract the index arguments from a constructor's elaborated type by peeling
-- Pi binders until reaching the data type application.
extractConIndexArgs ::
    Context -> Expression -> [Expression] -> Identifier -> Elab (Maybe [Expression])
extractConIndexArgs context expr paramArgs dataTypeName = do
    let env = contextEnv context
        w = evaluateWeakHeadNormalForm env expr
    case w of
        Pi _ _ _ codom -> extractConIndexArgs context codom paramArgs dataTypeName
        NatType | dataTypeName == Identifier "Nat" -> pure (Just [])
        VoidType | dataTypeName == Identifier "Void" -> pure (Just [])
        other ->
            let (headExpr, allArgs) = unfoldApp other
             in case headExpr of
                    Variable dt
                        | dt == dataTypeName ->
                            let numParams = length paramArgs
                                (_, cargs) = splitAt numParams allArgs
                             in pure (Just (map snd cargs))
                    _ -> pure Nothing

-- | Unify each constructor index arg with the corresponding target index arg.
unifyIndexArgs :: Context -> [Expression] -> [Expression] -> Elab ()
unifyIndexArgs _ [] [] = pure ()
unifyIndexArgs context (c : cs) (t : ts) = do
    unify context c t
    unifyIndexArgs context cs ts
unifyIndexArgs _ _ _ = pure ()

checkBranch ::
    Context ->
    Expression ->
    DataInfo ->
    [Expression] ->
    [Expression] ->
    Identifier ->
    Expression ->
    Maybe (Identifier, Expression) ->
    Expression ->
    CaseBranch ->
    Elab CaseBranch
checkBranch context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType (CaseBranch pat body) = do
    let (con, vars) = case pat of
            PatCon c ps -> (c, [case p of { PatVar v -> v; _ -> Identifier ("_pat" <> Text.pack (show i)) } | (i, p) <- zip [(0 :: Int) ..] ps])
            PatVar c -> (c, [])
            _ -> (Identifier "_", [])
    if con == Identifier "_"
        then do
            let extContext = case pat of
                    PatVar v -> extendContextType v whnfTargetType context
                    _ -> context
            elabBody <- checkElab extContext body expType
            pure (CaseBranch pat elabBody)
        else do
            checked <- checkConstructorBranch context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType con vars body
            pure checked { branchPattern = pat }

checkConstructorBranch context elabTarget dataInfo paramArgs indexArgs dataTypeName whnfTargetType mMotive expType con vars body = do
    localConType <-
        case lookup con (dataConstructors dataInfo) of
            Just ty -> pure ty
            Nothing -> throwError (UnknownConstructor dataTypeName con)
    let paramNames = map (\(_, p, _) -> p) (dataParams dataInfo)
        conSubst = foldr (\(p, a) acc -> substitute p a acc) localConType (zip paramNames paramArgs)
    (explicitArgTypes, _) <- peelConstructorArgs context vars conSubst
    fallbackArgTypes <- mapM (\_ -> freshMeta context (Universe (UFixed (-1)))) (drop (length explicitArgTypes) vars)
    let allArgTypes = explicitArgTypes ++ fallbackArgTypes
    let extContext =
            foldr (\(v, ty) ctx -> extendContextType v ty ctx) context (zip vars allArgTypes)
        conApp =
            case dataTypeName of
                Identifier "Nat" ->
                    if con == Identifier "zero"
                        then Zero
                        else foldl (Application Explicit) Succ (map Variable vars)
                _ ->
                    foldl
                        (Application Explicit)
                        (foldl
                            (Application Implicit)
                            (Variable con)
                            indexArgs
                        )
                        (map Variable vars)
        (refContext, branchExpected) =
            case (elabTarget, mMotive) of
                (Variable targetVar, Just (mv, mtype)) ->
                    ( extendContextDefinition targetVar whnfTargetType conApp extContext
                    , substitute targetVar conApp (substitute mv conApp mtype)
                    )
                (Variable targetVar, Nothing) ->
                    ( extendContextDefinition targetVar whnfTargetType conApp extContext
                    , substitute targetVar conApp expType
                    )
                (_, Just (mv, mtype)) ->
                    (extContext, substitute mv conApp mtype)
                _ -> (extContext, expType)
    elabBody <- checkElab refContext body branchExpected
    pure (CaseBranch (PatCon con (map PatVar vars)) elabBody)

compilePatternCase :: Context -> Expression -> [(Pattern, Expression)] -> Elab [CaseBranch]
compilePatternCase context target clauses = do
    (_, targetType) <- synthesizeElab context target
    let (headType, _) = unfoldApp targetType
        constructors = case headType of
            Variable name -> maybe [] (map fst . dataConstructors) (Map.lookup name (contextData context))
            NatType -> [Identifier "zero", Identifier "successor"]
            _ -> []
        constructorArity name = case Map.lookup name (contextData context) >>= lookup name . dataConstructors of
            Nothing | name == Identifier "zero" -> 0
            Nothing | name == Identifier "successor" -> 1
            Nothing -> 0
            Just ty -> countExplicit ty
        countExplicit ty = case evaluateWeakHeadNormalForm (contextEnv context) ty of
            Pi Explicit _ _ codom -> 1 + countExplicit codom
            Pi _ _ _ codom -> countExplicit codom
            _ -> 0
        freshArgs name = [Identifier ("pat" <> Text.pack (show i)) | i <- [0 .. constructorArity name - 1]]
        expandWild body =
            [ CaseBranch (PatCon con (map PatVar (freshArgs con))) body | con <- constructors ]
        literalPattern n
            | n <= 0 = PatCon (Identifier "zero") []
            | otherwise = PatCon (Identifier "successor") [literalPattern (n - 1)]
        tuplePattern [] = PatCon (Identifier "unit") []
        tuplePattern [p] = p
        tuplePattern (p : ps) = PatCon (Identifier "pair") [p, tuplePattern ps]
        compileAt scrutinee pattern body = case pattern of
            PatVar name -> Let name Nothing scrutinee body
            PatWild -> body
            PatLit (LitNat n) -> compileAt scrutinee (literalPattern n) body
            PatTuple ps -> compileAt scrutinee (tuplePattern ps) body
            PatCon con subpatterns ->
                let args = [Identifier ("pat" <> Text.pack (show i)) | i <- [0 .. length subpatterns - 1]]
                    nested = foldr (\(arg, subpattern) acc -> compileAt (Variable arg) subpattern acc) body (zip args subpatterns)
                 in Case scrutinee Nothing [CaseBranch (PatCon con (map PatVar args)) nested]
        compileTop pattern body = case pattern of
            PatVar name -> expandWild (substitute name target body)
            PatWild -> expandWild body
            PatLit (LitNat n) -> compileTop (literalPattern n) body
            PatTuple ps -> compileTop (tuplePattern ps) body
            PatCon con subpatterns ->
                let args = [Identifier ("pat" <> Text.pack (show i)) | i <- [0 .. length subpatterns - 1]]
                    nested = foldr (\(arg, subpattern) acc -> compileAt (Variable arg) subpattern acc) body (zip args subpatterns)
                 in [CaseBranch (PatCon con (map PatVar args)) nested]
    pure (concatMap (uncurry compileTop) clauses)

primitiveOpType :: PrimOp -> Expression
primitiveOpType operation = case operation of
    NatToInt -> unary NatType (PrimType PTInt)
    IntNeg -> unary (PrimType PTInt) (PrimType PTInt)
    FloatNeg -> unary (PrimType PTFloat) (PrimType PTFloat)
    IntAdd -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt); IntSub -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt); IntMul -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt); IntPow -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntDiv -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt); IntMod -> binary (PrimType PTInt) (PrimType PTInt) (PrimType PTInt)
    IntEq -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool")); IntNeq -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool")); IntLt -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool")); IntLe -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool")); IntGt -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool")); IntGe -> binary (PrimType PTInt) (PrimType PTInt) (Variable (Identifier "Bool"))
    BoolEq -> binary (Variable (Identifier "Bool")) (Variable (Identifier "Bool")) (Variable (Identifier "Bool"))
    FloatAdd -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat); FloatSub -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat); FloatMul -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat); FloatDiv -> binary (PrimType PTFloat) (PrimType PTFloat) (PrimType PTFloat)
    FloatEq -> binary (PrimType PTFloat) (PrimType PTFloat) (Variable (Identifier "Bool")); FloatLt -> binary (PrimType PTFloat) (PrimType PTFloat) (Variable (Identifier "Bool")); FloatLe -> binary (PrimType PTFloat) (PrimType PTFloat) (Variable (Identifier "Bool"))
    StringAppend -> binary (PrimType PTString) (PrimType PTString) (PrimType PTString); StringEq -> binary (PrimType PTString) (PrimType PTString) (Variable (Identifier "Bool"))
    CharEq -> binary (PrimType PTChar) (PrimType PTChar) (Variable (Identifier "Bool"))
    IntToFloat -> unary (PrimType PTInt) (PrimType PTFloat); FloatToInt -> unary (PrimType PTFloat) (PrimType PTInt); FloatTruncate -> unary (PrimType PTFloat) (PrimType PTInt)
    CharToInt -> unary (PrimType PTChar) (PrimType PTInt); IntToChar -> unary (PrimType PTInt) (PrimType PTChar)
    StringLength -> unary (PrimType PTString) NatType; StringToList -> unary (PrimType PTString) (Variable (Identifier "List")); ListToString -> unary (Variable (Identifier "List")) (PrimType PTString)
    IntToString -> unary (PrimType PTInt) (PrimType PTString); FloatToString -> unary (PrimType PTFloat) (PrimType PTString); CharToString -> unary (PrimType PTChar) (PrimType PTString)
    FloatSqrt -> unary (PrimType PTFloat) (PrimType PTFloat); FloatSin -> unary (PrimType PTFloat) (PrimType PTFloat); FloatCos -> unary (PrimType PTFloat) (PrimType PTFloat); FloatExp -> unary (PrimType PTFloat) (PrimType PTFloat); FloatLog -> unary (PrimType PTFloat) (PrimType PTFloat)
    StringIndex -> binary (PrimType PTString) NatType (Variable (Identifier "Maybe")); StringSlice -> binary (PrimType PTString) (PrimType PTInt) (PrimType PTString)
    IntFold -> Pi Implicit (Identifier "A") (Universe (UFixed (-1))) (Pi Explicit (Identifier "n") (PrimType PTInt) (Pi Explicit (Identifier "z") (Variable (Identifier "A")) (Pi Explicit (Identifier "step") (Pi Explicit (Identifier "_") (PrimType PTInt) (Pi Explicit (Identifier "_") (Variable (Identifier "A")) (Variable (Identifier "A")))) (Variable (Identifier "A")))))
  where
    unary domain codomain = Pi Explicit (Identifier "_") domain codomain
    binary left right codomain = Pi Explicit (Identifier "_") left (Pi Explicit (Identifier "_") right codomain)
    maybeType element = Application Explicit (Variable (Identifier "Maybe")) element

-- Numeric operators are kept as ordinary prelude names for Nat, but their
-- saturated applications are elaborated here so the concrete primitive type
-- of either operand can drive promotion before the old Nat definition is
-- consulted.
numericOperator :: Identifier -> Bool
numericOperator name = name `elem`
    map Identifier ["+" , "-", "*", "/", "^", "==", "/=", "<", "<=", ">", ">=", "++"]

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
        let leftNat = leftType == NatType
            rightNat = rightType == NatType
            leftPrim = numericKind leftType
            rightPrim = numericKind rightType
            resultKind = case (leftPrim, rightPrim) of
                (Just PTFloat, _) -> Just PTFloat
                (_, Just PTFloat) -> Just PTFloat
                (Just PTInt, _) -> Just PTInt
                (_, Just PTInt) -> Just PTInt
                (Just PTString, Just PTString) -> Just PTString
                (Just PTChar, Just PTChar) -> Just PTChar
                _ | leftNat && rightNat -> Nothing
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
            Nothing
                | leftNat && rightNat ->
                    pure (Application Explicit (Application Explicit (Variable op) elabLeft) elabRight,
                          if comparison then Variable (Identifier "Bool") else NatType)
                | otherwise -> throwError (TypeMismatch leftType rightType)

peelConstructorArgs :: Context -> [Identifier] -> Expression -> Elab ([Expression], Expression)
peelConstructorArgs _ [] ty = pure ([], ty)
peelConstructorArgs ctx (v : vs) ty = do
    let env = contextEnv ctx
        wTy = evaluateWeakHeadNormalForm env ty
    case wTy of
        Pi Explicit param dom codom -> do
            (rest, finalCodom) <- peelConstructorArgs ctx vs (substitute param (Variable v) codom)
            pure (dom : rest, finalCodom)
        Pi Implicit param _ codom -> do
            m <- freshMeta ctx (Universe (UFixed (-1)))
            peelConstructorArgs ctx (v : vs) (substitute param m codom)
        Pi Instance param _ codom -> do
            m <- freshMeta ctx (Universe (UFixed (-1)))
            peelConstructorArgs ctx (v : vs) (substitute param m codom)
        other ->
            throwError (ExpectedFunctionType other)

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
    NatType -> pure (NatType, Universe (UFixed (-1)))
    Zero -> pure (Zero, NatType)
    -- The constructor itself remains Nat -> Nat so higher-order Nat proofs
    -- (for example `congruence successor ih`) infer the inductive operation.
    -- Applications are specialized to Int by the application rule below.
    Succ -> pure (Succ, succType)
    NatRec -> pure (NatRec, natRecType)
    Literal (LitNat n) -> pure (Literal (LitNat n), NatType)
    Literal (LitInt _) -> pure (expression, PrimType PTInt)
    Literal (LitFloat _) -> pure (expression, PrimType PTFloat)
    Literal (LitChar _) -> pure (expression, PrimType PTChar)
    Literal (LitString _) -> pure (expression, PrimType PTString)
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
    PatternCase target mMotive branches -> do
        retMeta <- freshMeta context (Universe (UFixed (-1)))
        compiled <- compilePatternCase context target branches
        elabCase <- checkElab context (Case target mMotive compiled) retMeta
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
    RecordLiteral recordName fieldValues -> do
        recInfo <- case Map.lookup recordName (contextRecords context) of
            Just info -> pure info
            Nothing -> throwError (UnboundVariable recordName)
        let valueMap = Map.fromList fieldValues
        ordered <- traverse (\field ->
            case Map.lookup (recordFieldName field) valueMap of
                Just value -> pure value
                Nothing -> throwError (UnknownField (recordFieldName field) recordName)) (recordFields recInfo)
        let constructor = Variable (recordConName recInfo)
            applied = foldl (Application Explicit) constructor ordered
        synthesizeElab context applied
    Application Explicit (Application Explicit (Variable op) left) right
        | numericOperator op -> numericBinary context op left right
    Application Explicit successorExpr argument
        | isSuccessorExpression successorExpr -> do
            (elabArg, argType0) <- synthesizeElab context argument
            argType <- zonk argType0
            let argWhnf = evaluateWeakHeadNormalForm (contextEnv context) argType
            case argWhnf of
                NatType -> pure (Application Explicit Succ elabArg, NatType)
                PrimType PTInt -> pure (intSuccessorExpression elabArg, PrimType PTInt)
                _ -> throwError (TypeMismatch NatType argWhnf)
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
            (Literal (LitNat n), NatType) -> pure (Literal (LitNat n))
            (Literal (LitNat n), PrimType PTInt) -> pure (Literal (LitInt n))
            (Literal (LitNat n), PrimType PTFloat) -> pure (Literal (LitFloat (fromIntegral n)))
            (Literal (LitInt n), NatType)
                | n >= 0 -> pure (Literal (LitNat n))
                | otherwise -> throwError (TypeMismatch NatType (PrimType PTInt))
            (Literal (LitInt n), PrimType PTInt) -> pure (Literal (LitInt n))
            (Literal (LitInt n), PrimType PTFloat) -> pure (Literal (LitFloat (fromIntegral n)))
            (Literal (LitFloat n), PrimType PTFloat) -> pure (Literal (LitFloat n))
            (Literal (LitChar c), PrimType PTChar) -> pure (Literal (LitChar c))
            (Literal (LitString s), PrimType PTString) -> pure (Literal (LitString s))
            (Hole mName, _) -> do
                mId <- freshMetaId
                recordMeta mId mName context zonkedExpected
                pure (MetaVar mId)
            (Case target mMotive branches, _) -> do
                (elabTarget, rawTargetType) <- synthesizeElab context target
                zonkedTargetType <- zonk rawTargetType
                let whnfTargetType = evaluateWeakHeadNormalForm env zonkedTargetType
                elabBranches <- checkCaseBranches context elabTarget whnfTargetType whnfExpected mMotive branches
                pure (Case elabTarget mMotive elabBranches)
            (PatternCase target mMotive branches, _) -> do
                (elabTarget, rawTargetType) <- synthesizeElab context target
                compiled <- compilePatternCase context elabTarget branches
                checkElab context (Case elabTarget mMotive compiled) expType
            (Succ, Pi Explicit _ NatType _) -> pure Succ
            (Application Explicit successorExpr argument, PrimType PTInt)
                | isSuccessorExpression successorExpr -> do
                    (elabArg, argType) <- synthesizeElab context argument
                    argZonked <- zonk argType
                    let argWhnf = evaluateWeakHeadNormalForm env argZonked
                    case argWhnf of
                        PrimType PTInt -> pure (intSuccessorExpression elabArg)
                        NatType -> pure (intSuccessorExpression (Application Explicit (PrimOp NatToInt) elabArg))
                        _ -> throwError (TypeMismatch (PrimType PTInt) argWhnf)
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
            (Lambda _ _ _ _, notPiType) ->
                throwError (ExpectedFunctionType notPiType)
            (otherExpression, _) -> do
                (elabExpr, synthesizedType) <- synthesizeElab context otherExpression
                let actual = evaluateWeakHeadNormalForm env synthesizedType
                    expected = evaluateWeakHeadNormalForm env zonkedExpected
                    coerced = case (actual, expected) of
                        (NatType, PrimType PTInt) -> Just (Application Explicit (PrimOp NatToInt) elabExpr)
                        (PrimType PTInt, PrimType PTFloat) -> Just (Application Explicit (PrimOp IntToFloat) elabExpr)
                        (NatType, PrimType PTFloat) -> Just (Application Explicit (PrimOp IntToFloat) (Application Explicit (PrimOp NatToInt) elabExpr))
                        _ -> Nothing
                case coerced of
                    Just term -> pure term
                    Nothing -> unify context synthesizedType zonkedExpected >> pure elabExpr
  where
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

-- | Peel Pi binders from a data's declared universe until reaching `Universe lvl`,
-- returning the index binders and the universe level.
peelIndexTelescope :: Context -> Expression -> Elab ([(Visibility, Identifier, Expression)], UniverseLevel)
peelIndexTelescope ctx expr = go expr []
  where
    go e acc = do
        let env = contextEnv ctx
            w = evaluateWeakHeadNormalForm env e
        case w of
            Pi vis p ty codom -> go codom ((vis, p, ty) : acc)
            Universe lvl -> pure (reverse acc, lvl)
            other -> throwError (ExpectedUniverse other)

-- | Strict positivity check: a data type may not occur negatively (bare, as the
-- domain of an arrow) in any of its constructor types. Occurrences applied to
-- variables (parameters/indices) are permitted, since they describe the
-- structural arguments being consumed.
checkPositive :: Identifier -> Expression -> Elab ()
checkPositive dataName expr = go False expr
  where
    go inDomain e = case e of
        Pi _ _ dom codom ->
            go True dom >> go inDomain codom
        Variable ident
            | ident == dataName && inDomain ->
                throwError (NonStrictlyPositive dataName ident)
        Application _ f a ->
            case f of
                Variable ident | ident == dataName -> go inDomain a
                _ -> go inDomain f >> go inDomain a
        Lambda _ _ _ body -> go inDomain body
        Let _ _ d b -> go inDomain d >> go inDomain b
        Case t _mMotive branches ->
            go inDomain t >> mapM_ (go inDomain . branchBody) branches
        Annotation t _ -> go inDomain t
        _ -> pure ()

-- | Structural termination check: every recursive call to `name` must apply at
-- least one argument that is a structurally smaller variable (a constructor
-- subterm obtained by pattern matching on a parameter). Variables bound by the
-- function's own lambda parameters are tracked as `params`; variables bound by
-- case patterns on a parameter are tracked as `small` (strictly smaller).
checkTermination :: Identifier -> Expression -> Either TypeError ()
checkTermination name body =
    if Set.member name (freeVariables body)
        then checkCalls name Set.empty Set.empty Set.empty body
        else pure ()
  where
    checkCalls :: Identifier -> Set.Set Identifier -> Set.Set Identifier -> Set.Set Identifier -> Expression -> Either TypeError ()
    checkCalls nm params small guarded expr = case expr of
        Lambda _ pname _ bdy ->
            checkCalls nm (Set.insert pname params) small guarded bdy
        Case target _mMotive branches ->
            let targetVar = case target of Variable v -> Just v; _ -> Nothing
                small' = case targetVar of
                    Just v
                        | Set.member v params || Set.member v small ->
                            Set.union small (Set.fromList (concatMap (patternNames . branchPattern) branches))
                    _ -> small
             in mapM_ (checkBranch' nm params small' guarded target branches) branches
          where
            checkBranch' n pp ss gg targetExpr allBranches (CaseBranch pat bdy) =
                let branchGuarded = integerGuard targetExpr allBranches pat gg
                 in checkCalls n pp (Set.union ss (Set.fromList (patternNames pat))) branchGuarded bdy
            patternNames (PatVar v) = [v]
            patternNames PatWild = []
            patternNames (PatLit _) = []
            patternNames (PatCon _ ps) = concatMap patternNames ps
            patternNames (PatTuple ps) = concatMap patternNames ps
        Application _ f arg ->
            let (h, spine) = unfoldApp expr
             in case h of
                    Variable ident | ident == nm ->
                        if any (\(_, a) -> isSmallerArgument params small guarded a) spine
                            then mapM_ (checkCalls nm params small guarded . snd) spine >> pure ()
                            else Left (NonTerminatingDefinition nm)
                    _ -> checkCalls nm params small guarded f >> checkCalls nm params small guarded arg
        Pi _ _ dom codom ->
            checkCalls nm params small guarded dom >> checkCalls nm params small guarded codom
        Let _ _ d b ->
            checkCalls nm params small guarded d >> checkCalls nm params small guarded b
        Annotation t _ -> checkCalls nm params small guarded t
        _ -> pure ()

    isSmallerArgument params small guarded argument =
        case argument of
            Variable v -> Set.member v small
            _ ->
                let (headExpr, arguments) = unfoldApp argument
                    explicitArguments = [value | (Explicit, value) <- arguments]
                 in case (headExpr, reverse explicitArguments) of
                        (Variable (Identifier "drop"), Variable v : _) -> Set.member v (Set.union params small)
                        _ -> False
                    || case (headExpr, explicitArguments) of
                        (PrimOp IntSub, [Variable v, Literal (LitInt k)]) ->
                            k >= 1 && Set.member v guarded
                        _ -> False

    integerGuard target branches pattern guards =
        case (stripLocated target, pattern) of
            (Application Explicit (Application Explicit (PrimOp IntLe) (Variable v)) (Literal (LitInt _)), PatCon con [])
                | con == Identifier "false" -> Set.insert v guards
            (Variable v, PatWild)
                | any (isPositiveBase . branchPattern) branches -> Set.insert v guards
            (Variable v, PatVar _)
                | any (isPositiveBase . branchPattern) branches -> Set.insert v guards
            _ -> guards

    isPositiveBase (PatLit (LitInt n)) = n >= 0
    isPositiveBase _ = False

    stripLocated (Located _ inner) = stripLocated inner
    stripLocated inner = inner

checkTerminationElab :: Identifier -> Expression -> Elab ()
checkTerminationElab nm b = case checkTermination nm b of
    Left err -> throwError err
    Right () -> pure ()

checkDataDeclaration ::
    Context ->
    Identifier ->
    [(Visibility, Identifier, Expression)] ->
    Expression ->
    [(Identifier, Expression)] ->
    Either TypeDiagnostic Context
checkDataDeclaration context dataName params univ constructors =
    let traceMsg = "while checking data declaration '" <> prettyIdentifier dataName <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (elabUniv, _) <- synthesizeElab context univ
                    (indices, lvl) <- peelIndexTelescope context elabUniv
                    let allArgs = params ++ indices
                        typeConType = foldr (\(vis, p, ty) codom -> Pi vis p ty codom) (Universe lvl) allArgs
                        contextWithType = extendContextType dataName typeConType context
                        paramContext =
                            foldr
                                (\(_, p, ty) ctx -> extendContextType p ty ctx)
                                contextWithType
                                allArgs
                    (localConstructors, fullConstructors) <-
                        unzip
                            <$> traverse
                                ( \(cName, cType) ->
                                    localTrace
                                        ("while checking constructor '" <> prettyIdentifier cName <> "'")
                                        (checkCon paramContext allArgs (cName, cType))
                                )
                                constructors
                    let dataInfo = DataInfo params indices elabUniv localConstructors
                        finalContext =
                            foldr
                                addConstructor
                                ( contextWithType
                                    { contextData =
                                        Map.insert dataName dataInfo (contextData contextWithType)
                                    }
                                )
                                fullConstructors
                    solveUnivConstraints
                    pure finalContext
            )
            (ElabState 0 Map.empty Map.empty Nothing [] 0 [])
  where
    checkCon pCtx allArgs (cName, cType) = do
        (elabCType, _) <- synthesizeElab pCtx cType
        _ <- checkPositive dataName elabCType
        let fullConType =
                foldr (\(_, p, ty) codom -> Pi Implicit p ty codom) elabCType allArgs
        pure ((cName, elabCType), (cName, fullConType))
    addConstructor (cName, cType) ctx =
        ctx
            { contextTypes = Map.insert cName cType (contextTypes ctx)
            , contextValues = Map.insert cName (Variable cName) (contextValues ctx)
            , contextEnv = Map.insert cName (VCon cName []) (contextEnv ctx)
            }

checkRecordDeclaration ::
    Context ->
    Identifier ->
    [(Visibility, Identifier, Expression)] ->
    Expression ->
    [RecordField] ->
    Maybe Identifier ->
    Either TypeDiagnostic Context
checkRecordDeclaration context recName params univ fields mConName =
    let traceMsg = "while checking record declaration '" <> prettyIdentifier recName <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (elabUniv, _) <- synthesizeElab context univ
                    (indices, lvl) <- peelIndexTelescope context elabUniv
                    let allArgs = params ++ indices
                        typeConType = foldr (\(vis, p, ty) codom -> Pi vis p ty codom) (Universe lvl) allArgs
                        contextWithType = extendContextType recName typeConType context
                        paramContext =
                            foldr
                                (\(_, p, ty) ctx -> extendContextType p ty ctx)
                                contextWithType
                                allArgs
                    let conName = fromMaybe (Identifier ("mk" <> unIdentifier recName)) mConName
                        conAppArgs = map (\(_, p, _) -> Variable p) allArgs
                        conApp = foldl (\acc x -> Application Explicit acc x) (Variable recName) conAppArgs
                        conRawType =
                            foldr
                                (\field acc -> Pi Explicit (recordFieldName field) (recordFieldType field) acc)
                                conApp
                                fields
                    _ <- checkPositive recName conRawType
                    (elabConType, _) <- synthesizeElab paramContext conRawType
                    let fullConType =
                            foldr (\(_, p, ty) codom -> Pi Implicit p ty codom) elabConType allArgs
                    let recordType = foldr (\(vis, p, ty) codom -> Pi vis p ty codom) (Universe lvl) allArgs
                        conVars = map recordFieldName fields
                        conValue = foldl (Application Explicit) (Variable conName) (map Variable conVars)
                        projectionFor field =
                            let recVar = Identifier "record"
                                branch = CaseBranch (PatCon conName (map PatVar conVars)) (Variable (recordFieldName field))
                                body = Lambda Explicit recVar Nothing (Case (Variable recVar) Nothing [branch])
                                value = foldr (\(_, p, _) b -> Lambda Implicit p Nothing b) body allArgs
                                ty = foldr (\(_, p, t) b -> Pi Implicit p t b)
                                         (Pi Explicit recVar (foldl (Application Explicit) (Variable recName) conAppArgs) (recordFieldType field))
                                         allArgs
                             in (recordFieldName field, ty, value)
                        projectionBindings = map projectionFor fields
                        ctxWithCon =
                            paramContext
                                { contextTypes = Map.insert conName fullConType (contextTypes paramContext)
                                , contextValues = Map.insert conName (Variable conName) (contextValues paramContext)
                                , contextEnv = Map.insert conName (VCon conName []) (contextEnv paramContext)
                                }
                        ctxWithProjections =
                            foldr (\(fieldName, fieldType, fieldValue) ctx ->
                                    extendContextDefinition fieldName fieldType fieldValue ctx)
                                  ctxWithCon projectionBindings
                    let recInfo =
                            RecordInfo
                                { recordName = recName
                                , recordParams = params
                                , recordUniverse = elabUniv
                                , recordFields = fields
                                , recordConName = conName
                                }
                        finalContext =
                            ctxWithProjections
                                { contextRecords =
                                    Map.insert recName recInfo (contextRecords ctxWithCon)
                                }
                    solveUnivConstraints
                    pure finalContext
            )
            (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

checkClassDeclaration :: Context -> Identifier -> [(Visibility, Identifier, Expression)] -> [RecordField] -> Either TypeDiagnostic Context
checkClassDeclaration context name params fields =
    checkRecordDeclaration context name params (Universe (UFixed (-1))) fields Nothing

checkClassDeclarationDetailed :: Context -> Identifier -> [(Visibility, Identifier, Expression)] -> [ClassMethod] -> Either TypeDiagnostic Context
checkClassDeclarationDetailed context name params methods =
    let fields = [RecordField (methodName m) (methodType m) | m <- methods]
        defaults = [(methodName m, body) | m <- methods, Just body <- [methodDefault m]]
     in do
        updated <- checkClassDeclaration context name params fields
        let makeInstanceType ty = case ty of
                Pi vis p dom (Pi Explicit dict dictTy rest) -> Pi vis p dom (Pi Instance dict dictTy rest)
                other -> other
            updatedTypes = foldr (\method ctx ->
                case Map.lookup (methodName method) (contextTypes ctx) of
                    Nothing -> ctx
                    Just ty -> ctx { contextTypes = Map.insert (methodName method) (makeInstanceType ty) (contextTypes ctx) })
                updated methods
        pure updatedTypes { contextClassDefaults = Map.insert name defaults (contextClassDefaults updatedTypes) }

checkInstanceDeclarationDetailed :: Context -> Identifier -> [(Visibility, Identifier, Expression)] -> Expression -> [Clause] -> Either TypeDiagnostic Context
checkInstanceDeclarationDetailed context className _params headType clauses = do
    info <- case Map.lookup className (contextRecords context) of
        Just x -> Right x
        Nothing -> Left (TypeDiagnostic Nothing [] (UnboundVariable className))
    field <- case recordFields info of
        (f : _) -> Right f
        [] -> Left (TypeDiagnostic Nothing [] (CannotSynthesizeType (Variable className)))
    let methodBody = compileClauses Nothing clauses
    checkInstanceDeclaration context className headType [(recordFieldName field, methodBody)]

checkInstanceDeclaration :: Context -> Identifier -> Expression -> [(Identifier, Expression)] -> Either TypeDiagnostic Context
checkInstanceDeclaration context className headType fields = do
    info <- case Map.lookup className (contextRecords context) of
        Just x -> Right x
        Nothing -> Left (TypeDiagnostic Nothing [] (UnboundVariable className))
    let instanceName = Identifier ("instance_" <> unIdentifier className <> "_" <> Text.pack (show headType))
        supplied = Map.fromList fields
        defaults = Map.fromList (Map.findWithDefault [] className (contextClassDefaults context))
        ordered = traverse (\f -> case Map.lookup (recordFieldName f) supplied of
                Just value -> Right value
                Nothing -> maybe (Left (TypeDiagnostic Nothing [] (UnknownField (recordFieldName f) className))) Right (Map.lookup (recordFieldName f) defaults)) (recordFields info)
        instanceType = Application Explicit (Variable className) headType
    values <- ordered
    let dict = foldl (Application Explicit) (Variable (recordConName info)) values
    (updated, _, _) <- checkDefinition context instanceName (Just instanceType) dict
    Right updated { contextInstances = Map.insertWith (++) className [instanceName] (contextInstances updated) }

synthesize :: Context -> Expression -> Either TypeDiagnostic (Expression, Expression, [Goal])
synthesize context rawExpr =
    evalStateT
        ( do
            (elabExpr, rawType) <- synthesizeElab context rawExpr
            zonkedType <- zonk rawType
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            solveUnivConstraints
            pure (zonkedExpr, zonkedType, goals)
        )
        (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

check :: Context -> Expression -> Expression -> Either TypeDiagnostic (Expression, [Goal])
check context rawExpr expType =
    evalStateT
        ( do
            (elabExpected, _) <- synthesizeElab context expType
            zonkedExpected <- zonk elabExpected
            elabExpr <- checkElab context rawExpr zonkedExpected
            zonkedExpr <- zonk elabExpr
            goals <- collectUnsolvedGoals
            solveUnivConstraints
            pure (zonkedExpr, goals)
        )
        (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

checkDefinition ::
    Context ->
    Identifier ->
    Maybe Expression ->
    Expression ->
    Either TypeDiagnostic (Context, Expression, [Goal])
checkDefinition context name maybeDeclaredType bodyTerm =
    checkDefinitionWithPartial False context name maybeDeclaredType bodyTerm

checkDefinitionWithPartial ::
    Bool ->
    Context ->
    Identifier ->
    Maybe Expression ->
    Expression ->
    Either TypeDiagnostic (Context, Expression, [Goal])
checkDefinitionWithPartial isPartial context name maybeDeclaredType bodyTerm =
    let traceMsg = "while checking definition '" <> prettyIdentifier name <> "'"
     in evalStateT
            ( localTrace traceMsg $
                do
                    (zonkedBody, finalType) <-
                        case maybeDeclaredType of
                            Just declaredType -> do
                                let generalizedType = generalizeType context declaredType
                                (elabDeclType, typeUniverse) <- synthesizeElab context generalizedType
                                _ <- extractUniverseLevel context typeUniverse
                                zonkedDeclType <- zonk elabDeclType
                                -- The name is in scope for its own body (so it can
                                -- refer to itself recursively), but only in
                                -- contextTypes, not contextValues, so it stays
                                -- neutral during typechecking and cannot diverge
                                -- the elaboration.
                                let recursiveContext = extendContextType name elabDeclType context
                                elabBody <- checkElab recursiveContext bodyTerm zonkedDeclType
                                zonkedBodyTerm <- zonk elabBody
                                unless isPartial (checkTerminationElab name zonkedBodyTerm)
                                zonkedFinalType <- zonk zonkedDeclType
                                pure (zonkedBodyTerm, zonkedFinalType)
                            Nothing -> do
                                (elabBody, rawType) <- synthesizeElab context bodyTerm
                                zonkedType <- zonk rawType
                                zonkedBodyTerm <- zonk elabBody
                                unless isPartial (checkTerminationElab name zonkedBodyTerm)
                                zonkedFinalType <- zonk zonkedType
                                pure (zonkedBodyTerm, zonkedFinalType)
                    goals <- collectUnsolvedGoals
                    solveUnivConstraints
                    let updatedContext = extendContextDefinition name finalType zonkedBody context
                    pure (updatedContext, finalType, goals)
            )
            (ElabState 0 Map.empty Map.empty Nothing [] 0 [])

checkFunctionDefinition :: Context -> Identifier -> Maybe Expression -> [Clause] -> Either TypeDiagnostic (Context, Expression, [Goal])
checkFunctionDefinition context name maybeDeclaredType clauses =
    checkFunctionDefinitionWithPartial False context name maybeDeclaredType clauses

checkFunctionDefinitionWithPartial :: Bool -> Context -> Identifier -> Maybe Expression -> [Clause] -> Either TypeDiagnostic (Context, Expression, [Goal])
checkFunctionDefinitionWithPartial isPartial context name maybeDeclaredType clauses =
    case clauses of
        [] -> Left (TypeDiagnostic Nothing [] (CannotSynthesizeType (Variable name)))
        firstClause : _
            | any ((/= length (clausePatterns firstClause)) . length . clausePatterns) clauses ->
                Left (TypeDiagnostic Nothing [] (ArityMismatch name (length (clausePatterns firstClause)) (length (clausePatterns (head clauses)))))
            | otherwise ->
                let generalizedType = fmap (generalizeType context) maybeDeclaredType
                 in checkDefinitionWithPartial isPartial context name generalizedType (compileClauses generalizedType clauses)

generalizeType :: Context -> Expression -> Expression
generalizeType context signature =
    foldr (\ident body -> Pi Implicit ident (Universe (UFixed (-1))) body)
        signature
        (freeTypeVariables context signature)

freeTypeVariables :: Context -> Expression -> [Identifier]
freeTypeVariables context expression =
    List.nub [ident | ident <- orderedFreeVars expression, isCandidate ident]
  where
    isCandidate ident@(Identifier name) =
        case Text.uncons name of
            Just (firstChar, _) -> isLower firstChar && Map.notMember ident (contextTypes context)
            Nothing -> False

    orderedFreeVars expr = case expr of
        Variable ident -> [ident]
        Pi _ parameter domain codomain ->
            orderedFreeVars domain ++ filter (/= parameter) (orderedFreeVars codomain)
        Application _ function argument -> orderedFreeVars function ++ orderedFreeVars argument
        Annotation term ty -> orderedFreeVars term ++ orderedFreeVars ty
        Tuple terms -> concatMap orderedFreeVars terms
        Located _ inner -> orderedFreeVars inner
        _ -> []

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
    UnknownField (Identifier field) (Identifier recordName) ->
        "Unknown field '" <> field <> "' on record '" <> recordName <> "'"
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
