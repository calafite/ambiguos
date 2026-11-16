{-# LANGUAGE OverloadedStrings #-}

module TypeChecker.Universe
    ( freshUnivVar
    , addUnivConstraint
    , extractUniverseLevel
    , peelIndexTelescope
    , solveUnivConstraints
    , checkConstraints
    ) where

import AST
    ( Expression (..)
    , Identifier (..)
    , UniverseLevel (..)
    , Visibility (..)
    )
import Control.Monad (foldM)
import Control.Monad.State.Strict (gets, modify)
import Data.Text (Text)
import qualified Data.Text as Text
import Evaluation (evaluateWeakHeadNormalForm)
import TypeChecker.Meta (solvePattern, zonk)
import TypeChecker.Types
    ( Context (..)
    , Elab
    , ElabState (..)
    , TypeError (..)
    , UnivConstraint (..)
    , throwError
    )

freshUnivVar :: Elab Int
freshUnivVar = do
    idx <- gets nextUnivVar
    modify (\s -> s{nextUnivVar = idx + 1})
    pure idx

addUnivConstraint :: UnivConstraint -> Elab ()
addUnivConstraint c = modify (\s -> s{univConstraints = c : univConstraints s})

extractUniverseLevel :: Context -> Expression -> Elab Int
extractUniverseLevel context expr = do
    z <- zonk expr
    let env = contextEnv context
        w = evaluateWeakHeadNormalForm env z
    case w of
        Universe lvl -> pure (levelToInt lvl)
        MetaVar i -> do
            solvePattern context i [] (Universe (UFixed (-1)))
            pure (-1)
        other -> throwError (ExpectedUniverse other)
  where
    levelToInt (UFixed n) = n
    levelToInt (UVar _) = -1
    levelToInt (UMax l1 l2) = max (levelToInt l1) (levelToInt l2)
    levelToInt (USucc l) = levelToInt l + 1

-- | Peel Pi binders from a data's declared universe until reaching `Universe lvl`,
-- returning the index binders and the universe level.
peelIndexTelescope :: Context -> Expression -> Elab ([(Visibility, Identifier, Expression)], UniverseLevel)
peelIndexTelescope ctx expr = go expr []
  where
    go e acc = do
        let env = contextEnv ctx
            w = evaluateWeakHeadNormalForm env e
        case w of
            Pi vis p ty codom -> go codom ((vis, p, ty) : acc)
            Universe lvl -> pure (reverse acc, lvl)
            other -> throwError (ExpectedUniverse other)

-- | Solve universe level constraints. Collects all constraints from the
-- elaboration state, flattens UMax/USucc into difference constraints, and
-- checks for inconsistencies (e.g., Type : Type would create 0 <= -1).
solveUnivConstraints :: Elab ()
solveUnivConstraints = do
    constraints <- gets univConstraints
    case checkConstraints constraints of
        Left msg -> throwError (UniverseInconsistency msg)
        Right () -> pure ()

-- | Check a list of universe constraints. Returns Left with an error message
-- if any constraint is violated.
checkConstraints :: [UnivConstraint] -> Either Text ()
checkConstraints = foldM checkConstraint ()
  where
    checkConstraint () (ULeq l1 l2) = checkLeq l1 l2 0
    checkConstraint () (ULt l1 l2) = checkLeq l1 l2 (-1)

    -- | Check l1 <= l2 + c.
    checkLeq l1 l2 c = case levelValue l1 of
        Just v1 -> case levelValue l2 of
            Just v2 ->
                if v1 <= v2 + c
                    then Right ()
                    else Left
                        ( "Universe level inconsistency: "
                            <> prettyUnivLevel l1
                            <> " <= "
                            <> prettyUnivLevel l2
                            <> " + "
                            <> Text.pack (show c)
                        )
            Nothing -> Right ()  -- Can't fully check l2 yet; assume OK
        Nothing -> Right ()  -- Can't fully check l1 yet; assume OK

    -- | Compute the integer value of a universe level, if fully determined.
    levelValue :: UniverseLevel -> Maybe Int
    levelValue (UFixed n) = Just n
    levelValue (UVar _) = Nothing
    levelValue (UMax l1 l2) = max <$> levelValue l1 <*> levelValue l2
    levelValue (USucc l) = (+1) <$> levelValue l

    -- | Pretty-print a universe level for error messages.
    prettyUnivLevel :: UniverseLevel -> Text
    prettyUnivLevel (UFixed n) = Text.pack (show n)
    prettyUnivLevel (UVar u) = "?u" <> Text.pack (show u)
    prettyUnivLevel (UMax l1 l2) = "max(" <> prettyUnivLevel l1 <> "," <> prettyUnivLevel l2 <> ")"
    prettyUnivLevel (USucc l) = "succ(" <> prettyUnivLevel l <> ")"
