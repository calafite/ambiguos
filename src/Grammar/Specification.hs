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
                , TokenBackslash
                , TokenArrow
                , TokenColon
                , TokenEquals
                , TokenLeftParen
                , TokenRightParen
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
                , TerminalSymbol TokenColon
                , NonTerminalSymbol ExpressionNT
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
            , Production
                LambdaNT
                [ TerminalSymbol TokenBackslash
                , TerminalSymbol TokenLeftParen
                , NonTerminalSymbol AtomNT
                , TerminalSymbol TokenColon
                , NonTerminalSymbol ExpressionNT
                , TerminalSymbol TokenRightParen
                , TerminalSymbol TokenArrow
                , NonTerminalSymbol ExpressionNT
                ]
            , Production AnnotationNT [NonTerminalSymbol ArrowNT]
            , Production
                AnnotationNT
                [ NonTerminalSymbol ArrowNT
                , TerminalSymbol TokenColon
                , NonTerminalSymbol ExpressionNT
                ]
            , Production
                ArrowNT
                [ TerminalSymbol TokenLeftParen
                , NonTerminalSymbol AtomNT
                , TerminalSymbol TokenColon
                , NonTerminalSymbol ExpressionNT
                , TerminalSymbol TokenRightParen
                , TerminalSymbol TokenArrow
                , NonTerminalSymbol ExpressionNT
                ]
            , Production ArrowNT [NonTerminalSymbol ApplicationNT]
            , Production
                ArrowNT
                [ NonTerminalSymbol ApplicationNT
                , TerminalSymbol TokenArrow
                , NonTerminalSymbol ExpressionNT
                ]
            , Production ApplicationNT [NonTerminalSymbol AtomNT, NonTerminalSymbol ApplicationNT]
            , Production ApplicationNT [NonTerminalSymbol AtomNT]
            , Production AtomNT [TerminalSymbol TokenKeywordType]
            , Production AtomNT [TerminalSymbol TokenKeywordId]
            , Production AtomNT [TerminalSymbol TokenKeywordRefl]
            , Production AtomNT [TerminalSymbol TokenKeywordJ]
            , Production AtomNT [TerminalSymbol TokenKeywordVoid]
            , Production AtomNT [TerminalSymbol TokenKeywordAbort]
            , Production AtomNT [TerminalSymbol TokenKeywordNat]
            , Production AtomNT [TerminalSymbol TokenKeywordZero]
            , Production AtomNT [TerminalSymbol TokenKeywordSucc]
            , Production AtomNT [TerminalSymbol TokenKeywordNatRec]
            , Production
                AtomNT
                [ TerminalSymbol TokenLeftParen
                , NonTerminalSymbol ExpressionNT
                , TerminalSymbol TokenRightParen
                ]
            ]
        , cfgStartSymbol = ProgramNT
        }
