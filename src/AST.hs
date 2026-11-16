module AST (
    Identifier (..),
    Visibility (..),
    Associativity (..),
    Fixity (..),
    UniverseLevel (..),
    Literal (..),
    PrimType (..),
    PrimOp (..),
    Guard (..),
    GuardedRhs (..),
    Pattern (..),
    CaseBranch (..),
    Clause (..),
    Expression (..),
    RecordField (..),
    RecordInfo (..),
    Statement (..),
) where

import Data.Text (Text)
import Diagnostics (SourceSpan (..))

newtype Identifier = Identifier
    { unIdentifier :: Text
    }
    deriving (Eq, Ord, Show)

data Visibility
    = Explicit
    | Implicit
    | Instance
    deriving (Eq, Ord, Show)

data Associativity
    = AssocLeft
    | AssocRight
    | AssocNone
    deriving (Eq, Ord, Show)

data Fixity = Fixity
    { fixityAssoc :: !Associativity
    , fixityPrec  :: !Int
    }
    deriving (Eq, Ord, Show)

data UniverseLevel
    = UFixed !Int
    | UVar !Int
    | UMax !UniverseLevel !UniverseLevel
    | USucc !UniverseLevel
    deriving (Eq, Ord, Show)

data Literal
    = LitInt !Integer
    | LitFloat !Double
    | LitChar !Char
    | LitString !Text
    deriving (Eq, Show)

data PrimType
    = PTInt
    | PTFloat
    | PTChar
    deriving (Eq, Ord, Show)

data PrimOp
    = IntAdd | IntSub | IntMul | IntDiv | IntMod | IntPow | IntNeg
    | IntEq | IntNeq | IntLt | IntLe | IntGt | IntGe | BoolEq
    | IntFold
    | FloatAdd | FloatSub | FloatMul | FloatDiv | FloatNeg
    | FloatEq | FloatLt | FloatLe | FloatSqrt | FloatSin | FloatCos | FloatExp | FloatLog
    | NatToInt | IntToFloat | FloatToInt | FloatTruncate
    | CharEq | CharToInt | IntToChar
    | StringAppend | StringLength | StringEq | StringIndex | StringSlice
    | StringToList | ListToString
    | IntToString | FloatToString | CharToString
    deriving (Eq, Ord, Show)

-- | Guard for pattern matching: boolean condition or pattern guard.
data Guard
    = BoolGuard !Expression
    | PatGuard !Pattern !Expression
    deriving (Eq, Show)

-- | A right-hand side with its guards.
data GuardedRhs = GuardedRhs
    { guardedRhsGuards :: ![Guard]
    , guardedRhsBody   :: !Expression
    }
    deriving (Eq, Show)

-- | Pattern: variables, constructors, literals, as-patterns, lists, tuples.
data Pattern
    = PatVar !Identifier
    | PatWild
    | PatAs !Identifier !Pattern
    | PatLit !Literal
    | PatCon !Identifier ![Pattern]
    | PatTuple ![Pattern]
    | PatList ![Pattern]
    deriving (Eq, Show)

-- | A case branch with optional guards and where bindings.
data CaseBranch = CaseBranch
    { branchPattern :: !Pattern
    , branchRhss    :: ![GuardedRhs]
    , branchWhere   :: ![Statement]
    }
    deriving (Eq, Show)

-- | Record field declaration.
data RecordField = RecordField
    { recordFieldName :: !Identifier
    , recordFieldType :: !Expression
    }
    deriving (Eq, Show)

-- | Record information stored in the context.
data RecordInfo = RecordInfo
    { recordName      :: !Identifier
    , recordParams    :: ![(Visibility, Identifier, Expression)]
    , recordUniverse  :: !Expression
    , recordFields    :: ![RecordField]
    , recordConName   :: !Identifier
    }
    deriving (Eq, Show)

-- | Expressions in the core language.
data Expression
    = Variable Identifier
    | Universe UniverseLevel
    | Lambda Visibility Identifier (Maybe Expression) Expression
    | Application Visibility Expression Expression
    | Pi Visibility Identifier Expression Expression
    | Let Identifier (Maybe Expression) Expression Expression
    | Case Expression (Maybe (Identifier, Expression)) [CaseBranch]
    | Literal !Literal
    | PrimType !PrimType
    | PrimOp !PrimOp
    | Annotation Expression Expression
    | Identity
    | Reflexivity
    | J
    | VoidType
    | Abort
    | Hole (Maybe Identifier)
    | MetaVar Int
    | Located !SourceSpan !Expression
    | Projection !Expression !Identifier
    | RecordLiteral !Identifier ![(Identifier, Expression)]
    | Tuple ![Expression]
    deriving (Eq, Show)

-- | A clause: name, patterns, guarded right-hand sides, optional where bindings.
data Clause = Clause
    { clauseName   :: !Identifier
    , clausePats   :: ![Pattern]
    , clauseRhss   :: ![GuardedRhs]
    , clauseWhere  :: ![Statement]
    }
    deriving (Eq, Show)

-- | Top-level statements.
data Statement
    = TypeSignature !Identifier !Expression
    | Definition !Bool Identifier (Maybe Expression) Expression
    | FunctionClause !Clause
    | FunctionDefinition !Bool !Identifier !(Maybe Expression) ![Clause]
    | Evaluation Expression
    | DataDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [(Identifier, Expression)]
    | TypeAlias Identifier [(Visibility, Identifier, Expression)] Expression
    | FixityDeclaration !Associativity !Int ![Identifier]
    | RecordDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [RecordField] (Maybe Identifier)
    | ModuleHeader [Identifier]
    | ImportStmt !Bool ![Identifier] !(Maybe [Identifier]) !(Maybe Identifier)
    | ClassDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [RecordField] [(Identifier, [Clause])]
    | InstanceDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [(Identifier, [Clause])]
    deriving (Eq, Show)
