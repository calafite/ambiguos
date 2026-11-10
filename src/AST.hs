module AST (
    Identifier (..),
    Expression (..),
    Statement (..),
) where

import Data.Text (Text)

newtype Identifier = Identifier
    { unIdentifier :: Text
    }
    deriving (Eq, Ord, Show)

data Expression
    = Variable Identifier
    | Universe
    | Lambda Identifier (Maybe Expression) Expression
    | Application Expression Expression
    | Pi Identifier Expression Expression
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
    deriving (Eq, Show)

data Statement
    = Definition Identifier (Maybe Expression) Expression
    | Evaluation Expression
    deriving (Eq, Show)
