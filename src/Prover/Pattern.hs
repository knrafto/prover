module Prover.Pattern where

import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet

import Prover.Term

-- | A compiled pattern of a rewrite rule.
data Rule = Rule
  { ruleCtxLength :: Int
  , ruleHead      :: NameId
  , ruleArgs      :: [Pattern]
  , ruleRhs       :: Term
  } deriving (Show)

-- | A compiled pattern argument.
data Pattern
  = VarPat !Int
  | AxiomPat NameId [Pattern]
  | PairPat Pattern Pattern
  deriving (Show)

-- | Collect the vars assigned by a pattern.
patternVars :: Pattern -> IntSet
patternVars = \case
  VarPat i        -> IntSet.singleton i
  AxiomPat _ args -> IntSet.unions (map patternVars args)
  PairPat a b     -> IntSet.union (patternVars a) (patternVars b)

-- | Returns whether a rule can extract all variables in the context.
matchable :: Rule -> Bool
matchable rule =
  let n    = ruleCtxLength rule
      vars = IntSet.unions (map patternVars (ruleArgs rule))
  in all (`IntSet.member` vars) [0..n-1]
