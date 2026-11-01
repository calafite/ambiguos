module Grammar.Specification
  ( ambiguosCFG
  ) where

import qualified Data.Set as Set
import Grammar.Types
import Lexer (Token (..))

ambiguosCFG :: CFG
ambiguosCFG = CFG
  { cfgNonTerminals = Set.fromList
      [ ProgramNT
      , StatementNT
      , DefinitionNT
      , EvaluationNT
      , ExpressionNT
      , LambdaNT
      , AnnotationNT
      , ArrowNT
      , ApplicationNT
      , AtomNT
      ]
  , cfgTerminals = Set.fromList
      [ TokenKeywordDef
      , TokenKeywordType
      , TokenKeywordId
      , TokenKeywordRefl
      , TokenKeywordJ
      , TokenBackslash
      , TokenArrow
      , TokenColon
      , TokenEquals
      , TokenLeftParen
      , TokenRightParen
      ]
  , cfgProductions =
      [ -- Program -> Statement Program | epsilon
        Production ProgramNT [NonTerminalSymbol StatementNT, NonTerminalSymbol ProgramNT]
      , Production ProgramNT []

        -- Statement -> Definition | Evaluation
      , Production StatementNT [NonTerminalSymbol DefinitionNT]
      , Production StatementNT [NonTerminalSymbol EvaluationNT]

        -- Definition -> 'def' IDENT ':' Expression '=' Expression
      , Production DefinitionNT
          [ TerminalSymbol TokenKeywordDef
          , NonTerminalSymbol AtomNT
          , TerminalSymbol TokenColon
          , NonTerminalSymbol ExpressionNT
          , TerminalSymbol TokenEquals
          , NonTerminalSymbol ExpressionNT
          ]

        -- Evaluation -> Expression
      , Production EvaluationNT [NonTerminalSymbol ExpressionNT]

        -- Expression -> Lambda | Annotation
      , Production ExpressionNT [NonTerminalSymbol LambdaNT]
      , Production ExpressionNT [NonTerminalSymbol AnnotationNT]

        -- Lambda -> '\' IDENT '->' Expression | '\' '(' IDENT ':' Expression ')' '->' Expression
      , Production LambdaNT
          [ TerminalSymbol TokenBackslash
          , NonTerminalSymbol AtomNT
          , TerminalSymbol TokenArrow
          , NonTerminalSymbol ExpressionNT
          ]
      , Production LambdaNT
          [ TerminalSymbol TokenBackslash
          , TerminalSymbol TokenLeftParen
          , NonTerminalSymbol AtomNT
          , TerminalSymbol TokenColon
          , NonTerminalSymbol ExpressionNT
          , TerminalSymbol TokenRightParen
          , TerminalSymbol TokenArrow
          , NonTerminalSymbol ExpressionNT
          ]

        -- Annotation -> Arrow | Arrow ':' Expression
      , Production AnnotationNT [NonTerminalSymbol ArrowNT]
      , Production AnnotationNT
          [ NonTerminalSymbol ArrowNT
          , TerminalSymbol TokenColon
          , NonTerminalSymbol ExpressionNT
          ]

        -- Arrow -> '(' IDENT ':' Expression ')' '->' Expression | Application | Application '->' Expression
      , Production ArrowNT
          [ TerminalSymbol TokenLeftParen
          , NonTerminalSymbol AtomNT
          , TerminalSymbol TokenColon
          , NonTerminalSymbol ExpressionNT
          , TerminalSymbol TokenRightParen
          , TerminalSymbol TokenArrow
          , NonTerminalSymbol ExpressionNT
          ]
      , Production ArrowNT [NonTerminalSymbol ApplicationNT]
      , Production ArrowNT
          [ NonTerminalSymbol ApplicationNT
          , TerminalSymbol TokenArrow
          , NonTerminalSymbol ExpressionNT
          ]

        -- Application -> Atom Application | Atom
      , Production ApplicationNT [NonTerminalSymbol AtomNT, NonTerminalSymbol ApplicationNT]
      , Production ApplicationNT [NonTerminalSymbol AtomNT]

        -- Atom -> 'Type' | 'Id' | 'refl' | 'J' | '(' Expression ')'
      , Production AtomNT [TerminalSymbol TokenKeywordType]
      , Production AtomNT [TerminalSymbol TokenKeywordId]
      , Production AtomNT [TerminalSymbol TokenKeywordRefl]
      , Production AtomNT [TerminalSymbol TokenKeywordJ]
      , Production AtomNT
          [ TerminalSymbol TokenLeftParen
          , NonTerminalSymbol ExpressionNT
          , TerminalSymbol TokenRightParen
          ]
      ]
  , cfgStartSymbol = ProgramNT
  }
