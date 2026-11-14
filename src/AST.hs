module AST (
    Identifier (..),
    Visibility (..),
    Associativity (..),
    Fixity (..),
    CaseBranch (..),
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

data CaseBranch = CaseBranch
    { branchConstructor :: !Identifier
    , branchBindings :: ![Identifier]
    , branchBody :: !Expression
    }
    deriving (Eq, Show)

data Expression
    = Variable Identifier
    | Universe !Int
    | Lambda Visibility Identifier (Maybe Expression) Expression
    | Application Visibility Expression Expression
    | Pi Visibility Identifier Expression Expression
    | Let Identifier (Maybe Expression) Expression Expression
    | Case Expression (Maybe (Identifier, Expression)) [CaseBranch]
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
    deriving (Eq, Show)

data Statement
    = Definition Identifier (Maybe Expression) Expression
    | Evaluation Expression
    | DataDeclaration Identifier [(Visibility, Identifier, Expression)] Expression [(Identifier, Expression)]
    | FixityDeclaration !Associativity !Int ![Identifier]
    deriving (Eq, Show)
