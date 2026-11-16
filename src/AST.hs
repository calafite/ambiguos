module AST (
    Identifier (..),
    Visibility (..),
    Associativity (..),
    Fixity (..),
    UniverseLevel (..),
    Literal (..),
    PrimType (..),
    PrimOp (..),
    CaseBranch (..),
    RecordField (..),
    RecordInfo (..),
    ClassMethod (..),
    Pattern (..),
    Clause (..),
    Expression (..),
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

-- | Universe level representation.
--   UFixed n   = concrete level n (e.g., Type 0, Type 1)
--   UVar u     = level variable (for level polymorphism / typical ambiguity)
--   UMax l1 l2 = maximum of two levels
--   USucc l    = successor of a level (l + 1)
data UniverseLevel
    = UFixed !Int
    | UVar !Int
    | UMax !UniverseLevel !UniverseLevel
    | USucc !UniverseLevel
    deriving (Eq, Ord, Show)

data Literal
    = LitNat !Integer
    | LitInt !Integer
    | LitFloat !Double
    | LitChar !Char
    | LitString !Text
    deriving (Eq, Show)

data PrimType
    = PTInt
    | PTFloat
    | PTChar
    | PTString
    deriving (Eq, Ord, Show)

data PrimOp
    = IntAdd | IntSub | IntMul | IntDiv | IntMod | IntPow | IntNeg
    | IntEq | IntNeq | IntLt | IntLe | IntGt | IntGe
    | IntFold
    | FloatAdd | FloatSub | FloatMul | FloatDiv | FloatNeg
    | FloatEq | FloatLt | FloatLe | FloatSqrt | FloatSin | FloatCos | FloatExp | FloatLog
    | NatToInt | IntToFloat | FloatToInt | FloatTruncate
    | IntToNat | IntAbs | ClampToNat
    | CharEq | CharToInt | IntToChar
    | StringAppend | StringLength | StringEq | StringIndex | StringSlice
    | StringToList | ListToString
    | IntToString | FloatToString | CharToString
    deriving (Eq, Ord, Show)

data CaseBranch = CaseBranch
    { branchPattern :: !Pattern
    , branchBody :: !Expression
    }
    deriving (Eq, Show)

-- | Record field declaration: a named field with its type.
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
    , recordConName   :: !Identifier   -- ^ constructor name (default: mk<RecordName>)
    }
    deriving (Eq, Show)

data ClassMethod = ClassMethod
    { methodName :: !Identifier
    , methodType :: !Expression
    , methodDefault :: !(Maybe Expression)
    }
    deriving (Eq, Show)

data Pattern
    = PatVar !Identifier
    | PatWild
    | PatLit !Literal
    | PatCon !Identifier ![Pattern]
    | PatTuple ![Pattern]
    deriving (Eq, Show)

data Expression
    = Variable Identifier
    | Universe UniverseLevel
    | Lambda Visibility Identifier (Maybe Expression) Expression
    | Application Visibility Expression Expression
    | Pi Visibility Identifier Expression Expression
    | Let Identifier (Maybe Expression) Expression Expression
    | Case Expression (Maybe (Identifier, Expression)) [CaseBranch]
    | PatternCase Expression (Maybe (Identifier, Expression)) [(Pattern, Expression)]
    | Literal !Literal
    | PrimType !PrimType
    | PrimOp !PrimOp
    | Annotation Expression Expression
    | Identity
    | Reflexivity
    | J
    | VoidType
    | Abort
    | NatType
    | Zero
    | Succ
    | NatRec
    | Hole (Maybe Identifier)
    | MetaVar Int
    | Located !SourceSpan !Expression
    | Projection !Expression !Identifier   -- ^ expr.field postfix projection
    | RecordLiteral !Identifier ![(Identifier, Expression)]
    | Tuple ![Expression]
    deriving (Eq, Show)

data Clause = Clause
    { clauseName     :: !Identifier
    , clausePatterns :: ![Pattern]
    , clauseBody     :: !Expression
    }
    deriving (Eq, Show)

data Statement
    = Definition Identifier (Maybe Expression) Expression
    | TypeSignature !Identifier !Expression
    | FunctionClause !Clause
    | FunctionDefinition !Identifier !(Maybe Expression) ![Clause]
    | Evaluation Expression
    | DataDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [(Identifier, Expression)]
    | FixityDeclaration !Associativity !Int ![Identifier]
    | RecordDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [RecordField] (Maybe Identifier)
    | ModuleHeader [Identifier]
    | ImportStmt !Bool ![Identifier] !(Maybe [Identifier]) !(Maybe Identifier)
    | ClassDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [RecordField]
    | InstanceDeclaration Identifier Expression [(Identifier, Expression)]
    | ClassDeclarationDetailed Identifier [(Visibility, Identifier, Expression)] [ClassMethod]
    | InstanceDeclarationDetailed Identifier [(Visibility, Identifier, Expression)] Expression [Clause]
    deriving (Eq, Show)
