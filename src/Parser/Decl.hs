module Parser.Decl
    ( groupStatements
    ) where

import AST (Clause (..), Statement (..))

groupStatements :: [Statement] -> [Statement]
groupStatements [] = []
groupStatements (TypeSignature name sig : rest) =
    let (clauses, remaining) = span matching rest
        cs = [c | FunctionClause c <- clauses]
     in if null cs
            then TypeSignature name sig : groupStatements rest
            else FunctionDefinition False name (Just sig) cs : groupStatements remaining
  where
    matching (FunctionClause (Clause n _ _ _)) = n == name
    matching _ = False
groupStatements (FunctionClause c@(Clause name _ _ _) : rest) =
    let (matching, remaining) = span isMatching rest
     in FunctionDefinition False name Nothing (c : [cl | FunctionClause cl <- matching]) : groupStatements remaining
  where
    isMatching (FunctionClause (Clause n _ _ _)) = n == name
    isMatching _ = False
groupStatements (FunctionDefinition partial name mty clauses : rest) =
    let (matching, remaining) = span isMatching rest
     in FunctionDefinition partial name mty (clauses ++ [cl | FunctionClause cl <- matching]) : groupStatements remaining
  where
    isMatching (FunctionClause (Clause n _ _ _)) = n == name
    isMatching _ = False
groupStatements (stmt : rest) = stmt : groupStatements rest
