{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Types
    ( Goal (..)
    , MetaInfo (..)
    , DataInfo (..)
    , TypeError (..)
    , UnivConstraint (..)
    , TypeDiagnostic (..)
    , Context (..)
    , builtinData
    , emptyContext
    , extendContextType
    , extendContextDefinition
    , extendContextPartialDefinition
    , isFunctionExpression
    , lookupContext
    , ElabState (..)
    , Elab
    , throwError
    , liftEither
    , localSpan
    , localTrace
    , catchElab
    , tryElab
    ) where

import AST
    ( Expression (..)
    , Fixity (..)
    , Identifier (..)
    , RecordInfo (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad.State.Strict (StateT (..), gets, modify)
import Control.Monad.Trans (lift)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Diagnostics (SourceSpan (..))
import Evaluation
    ( Environment
    , Neutral (..)
    , Value (..)
    , emptyEnvironment
    , evaluate
    )
import Parser (defaultFixityEnv)
import TypeChecker.Primitives (primitiveTypes, primitiveValues)

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
    , contextRuntimeEnv :: Environment
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
        , contextRuntimeEnv =
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

extendContextType :: Identifier -> Expression -> Context -> Context
extendContextType identifier expressionType context =
    context
        { contextTypes = Map.insert identifier expressionType (contextTypes context)
        , contextEnv = Map.delete identifier (contextEnv context)
        , contextRuntimeEnv = Map.delete identifier (contextRuntimeEnv context)
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
            , contextRuntimeEnv = Map.insert identifier value (contextRuntimeEnv context)
            }

extendContextPartialDefinition :: Identifier -> Expression -> Expression -> Context -> Context
extendContextPartialDefinition identifier expressionType expressionValue context =
    let oldRuntimeEnv = contextRuntimeEnv context
        runtimeValue = if isFunctionExpression expressionValue
            then evaluate recursiveRuntimeEnv expressionValue
            else evaluate oldRuntimeEnv expressionValue
        recursiveRuntimeEnv = Map.insert identifier (evaluate recursiveRuntimeEnv expressionValue) oldRuntimeEnv
     in context
            { contextTypes = Map.insert identifier expressionType (contextTypes context)
            , contextValues = Map.insert identifier expressionValue (contextValues context)
            , contextEnv = Map.insert identifier (VNeutral (NVar identifier)) (contextEnv context)
            , contextRuntimeEnv = Map.insert identifier runtimeValue oldRuntimeEnv
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
