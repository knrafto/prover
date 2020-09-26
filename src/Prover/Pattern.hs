module Prover.Pattern where

import Control.Monad

import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet

import Prover.Syntax.Internal

-- | A compiled pattern of a rewrite rule.
data Rule = Rule
  { ruleCtxLength :: Int
  , ruleHead      :: NameId
  , ruleArgs      :: [Pattern]
  , ruleRhs       :: Term
  } deriving (Show)

-- | A compiled pattern argument.
data Pattern
  = VarArg !Int
  | IgnoreArg
  | AxiomArg NameId [Pattern]
  deriving (Show)

-- | Collect the vars assigned by a pattern.
patternVars :: Pattern -> IntSet
patternVars = \case
  VarArg i        -> IntSet.singleton i
  IgnoreArg       -> IntSet.empty
  AxiomArg _ args -> IntSet.unions (map patternVars args)

-- | Returns whether a rule can extract all variables in the context.
matchable :: Rule -> Bool
matchable rule =
  let n    = ruleCtxLength rule
      vars = IntSet.unions (map patternVars (ruleArgs rule))
  in all (`IntSet.member` vars) [0..n-1]

match :: Pattern -> Term -> Maybe (IntMap Term)
match arg t = case arg of
  VarArg i         -> Just (IntMap.singleton i t)
  IgnoreArg        -> Just IntMap.empty
  AxiomArg id args -> case t of
    App (Axiom h) termArgs | h == id && length args == length termArgs ->
      IntMap.unions <$> mapM (uncurry match) (zip args termArgs)
    _ -> Nothing

-- | Match a rule's pattern against a term, extract a term for the RHS if successful.
tryRewrite :: Term -> Rule -> Maybe Term
tryRewrite t rule = case t of
  App (Axiom h) termArgs
    | h == ruleHead rule && length (ruleArgs rule) <= length termArgs -> do
      let args = ruleArgs rule
      vars <- IntMap.unions <$> mapM (uncurry match) (zip args termArgs)
      let n          = ruleCtxLength rule
          ctxTerms   = [vars IntMap.! i | i <- [0..n-1]]
          extraTerms = drop (length args) termArgs
      return $ applyTerm (ruleRhs rule) (ctxTerms ++ extraTerms)
  _ -> Nothing

-- Match the first successful rule.
tryRewrites :: Term -> [Rule] -> Maybe Term
tryRewrites t = msum . map (tryRewrite t)
