module AST
  ( Identifier (..)
  , Expression (..)
  , Statement (..)
  ) where

import Data.Text (Text)

newtype Identifier = Identifier
  { unIdentifier :: Text
  } deriving (Eq, Ord, Show)

data Expression
  = Variable Identifier
  | Universe
  | Lambda Identifier Expression
  | Application Expression Expression
  | Pi Identifier Expression Expression
  | Annotation Expression Expression
  deriving (Eq, Show)

data Statement
  = Definition Identifier Expression Expression
  | Evaluation Expression
  deriving (Eq, Show)
