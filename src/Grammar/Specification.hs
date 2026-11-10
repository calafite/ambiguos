module Grammar.Specification (
    ambiguosCFG,
) where

import qualified Data.Set as Set
import Grammar.Types
import Lexer (Token (..))

ambiguosCFG :: CFG
ambiguosCFG =
    CFG
        { cfgNonTerminals =
            Set.fromList
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
        , cfgTerminals =
            Set.fromList
                [ TokenKeywordDef
                , TokenKeywordType
                , TokenKeywordId
                , TokenKeywordRefl
                , TokenKeywordJ
                , TokenKeywordVoid
                , TokenKeywordAbort
                , TokenKeywordNat
                , TokenKeywordZero
                , TokenKeywordSucc
                , TokenKeywordNatRec
                , TokenNatural 0
                , TokenBackslash
                , TokenArrow
                , TokenColon
                , TokenEquals
                , TokenLeftParen
                , TokenRightParen
                , TokenLeftBracket
                , TokenRightBracket
                , TokenComma
                ]
        , cfgProductions =
            [ Production ProgramNT [NonTerminalSymbol StatementNT, NonTerminalSymbol ProgramNT]
            , Production ProgramNT []
            , Production StatementNT [NonTerminalSymbol DefinitionNT]
            , Production StatementNT [NonTerminalSymbol EvaluationNT]
            , Production
                DefinitionNT
                [ TerminalSymbol TokenKeywordDef
                , NonTerminalSymbol AtomNT
                , TerminalSymbol TokenEquals
                , NonTerminalSymbol ExpressionNT
                ]
            , Production EvaluationNT [NonTerminalSymbol ExpressionNT]
            , Production ExpressionNT [NonTerminalSymbol LambdaNT]
            , Production ExpressionNT [NonTerminalSymbol AnnotationNT]
            , Production
                LambdaNT
                [ TerminalSymbol TokenBackslash
                , NonTerminalSymbol AtomNT
                , TerminalSymbol TokenArrow
                , NonTerminalSymbol ExpressionNT
                ]
            , Production AnnotationNT [NonTerminalSymbol ArrowNT]
            , Production ArrowNT [NonTerminalSymbol ApplicationNT]
            , Production ApplicationNT [NonTerminalSymbol AtomNT]
            , Production AtomNT [TerminalSymbol TokenKeywordType]
            , Production AtomNT [TerminalSymbol TokenKeywordNat]
            , Production AtomNT [TerminalSymbol TokenLeftBracket, TerminalSymbol TokenRightBracket]
            ]
        , cfgStartSymbol = ProgramNT
        }
