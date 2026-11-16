{-# LANGUAGE OverloadedStrings #-}

module TypeChecker
    ( TypeError (..)
    , TypeDiagnostic (..)
    , Goal (..)
    , Context (..)
    , DataInfo (..)
    , emptyContext
    , extendContextType
    , extendContextDefinition
    , checkDataDeclaration
    , checkRecordDeclaration
    , checkClassDeclaration
    , checkClassDeclarationDetailed
    , checkInstanceDeclaration
    , checkInstanceDeclarationDetailed
    , synthesize
    , check
    , checkDefinition
    , checkDefinitionWithPartial
    , checkFunctionDefinition
    , checkFunctionDefinitionWithPartial
    , lookupContext
    , renderTypeError
    , renderTypeDiagnostic
    , renderGoals
    ) where

import TypeChecker.Declarations
    ( check
    , checkClassDeclaration
    , checkClassDeclarationDetailed
    , checkDataDeclaration
    , checkDefinition
    , checkDefinitionWithPartial
    , checkFunctionDefinition
    , checkFunctionDefinitionWithPartial
    , checkInstanceDeclaration
    , checkInstanceDeclarationDetailed
    , checkRecordDeclaration
    , synthesize
    )
import TypeChecker.Diagnostics
    ( renderGoals
    , renderTypeDiagnostic
    , renderTypeError
    )
import TypeChecker.Types
    ( Context (..)
    , DataInfo (..)
    , Goal (..)
    , TypeDiagnostic (..)
    , TypeError (..)
    , emptyContext
    , extendContextDefinition
    , extendContextType
    , lookupContext
    )
