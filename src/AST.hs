module AST (
    Identifier (..),
    Visibility (..),
    Expression (..),
    Statement (..),
) where

import Data.Text (Text)

newtype Identifier = Identifier
    { unIdentifier :: Text
    }
    deriving (Eq, Ord, Show)

data Visibility
    = Explicit
    | Implicit
    deriving (Eq, Ord, Show)

data Expression
    = Variable Identifier
    | Universe !Int
    | Lambda Visibility Identifier (Maybe Expression) Expression
    | Application Visibility Expression Expression
    | Pi Visibility Identifier Expression Expression
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
    deriving (Eq, Show)

data Statement
    = Definition Identifier (Maybe Expression) Expression
    | Evaluation Expression
    deriving (Eq, Show)
