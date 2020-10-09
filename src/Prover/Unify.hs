module Prover.Unify where

import Control.Monad
import Data.List
import Data.Maybe

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State.Class
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Prettyprinter

import Prover.Monad
import Prover.Pattern
import Prover.Pretty
import Prover.Term

-- | Try to solve all constraints.
solveConstraints :: M ()
solveConstraints = do
  cs <- gets constraints
  modify $ \s -> s { constraints = [] }
  cs' <- go cs
  -- Report unsolved constraints
  forM_ cs' $ \(TopLevelConstraint r c) -> case c of
    Solved True  -> return ()
    Solved False -> do
      debugFields "type error" $
        [ "loc"  |: return (pretty r)
        ]
      emitError $ TypeError r
    _            -> do
      debugFields "unsolved constraint" $
        [ "loc"  |: return (pretty r)
        ]
      emitError $ UnsolvedConstraint r
  -- Report and clear unsolved metas
  metaIds <- gets unsolvedMetas
  modify $ \s -> s { unsolvedMetas = HashSet.empty }
  forM_ metaIds $ \id -> do
    r <- getState id metaRanges
    debugFields "unsolved meta" $
      [ "loc"  |: return (pretty r)
      , "meta" |: return (prettyMeta id)
      ]
    emitError $ UnsolvedMeta r id
  where
    go :: [TopLevelConstraint] -> M [TopLevelConstraint]
    go cs = do
      -- Loop until no more additional metas get solved
      unsolvedBefore <- gets (HashSet.size . unsolvedMetas)
      cs' <- mapM simplifyTopLevelConstraint cs
      unsolvedAfter <- gets (HashSet.size . unsolvedMetas)
      if unsolvedBefore == unsolvedAfter then return cs' else go cs'

simplifyTopLevelConstraint :: TopLevelConstraint -> M TopLevelConstraint
simplifyTopLevelConstraint (TopLevelConstraint r c) = TopLevelConstraint r <$> simplify c

-- | Simplify a constraint as much as possible. The resulting constraint should
-- not be able to be simplified more, except if a meta is instantiated.
simplify :: Constraint -> M Constraint
simplify = \case
  Solved b          -> return (Solved b)
  TermEq ctx ty a b -> unify ctx ty a b
  SpineEq ctx ty ts -> unifySpine ctx ty ts
  And cs            -> simplifyAnd <$> mapM simplify cs
  ExactlyOne cs     -> simplifyExactlyOne <$> mapM simplify cs
  Guarded guard c   -> guarded guard c

simplifyAnd :: [Constraint] -> Constraint
simplifyAnd cs = case concat <$> traverse clauses cs of
  Nothing  -> Solved False
  Just []  -> Solved True
  Just [c] -> c
  Just cs  -> And cs
  where
    clauses :: Constraint -> Maybe [Constraint]
    clauses = \case
      Solved False  -> Nothing
      Solved True   -> Just []
      And cs        -> Just cs
      c             -> Just [c]

simplifyExactlyOne :: [Constraint] -> Constraint
simplifyExactlyOne cs = case filter (not . isFalse) cs of
  []  -> Solved False
  [c] -> c
  _   -> ExactlyOne cs
  where
    isFalse :: Constraint -> Bool
    isFalse = \case
      Solved False -> True
      _            -> False

guarded :: Constraint -> Constraint -> M Constraint
guarded guard c = simplify guard >>= \case
  Solved False -> return (Solved False)
  Solved True  -> simplify c
  guard'       -> return (Guarded guard' c)

-- | Assign a term for a metavariable.
assignMeta :: MetaId -> Term -> M ()
assignMeta id t = do
  debugFields "assign meta" $
    [ "meta" |: return (prettyMeta id)
    , "term" |: prettyTerm C0 t
    ]
  modify $ \s -> s
    { metaTerms = HashMap.insert id t (metaTerms s)
    , unsolvedMetas = HashSet.delete id (unsolvedMetas s)
    }

-- | The result of a pattern match.
data MatchResult
  -- | The match succeeded, and we can extract terms for context variables.
  = Match (IntMap Term)
  | NoMatch
  | Blocked

instance Semigroup MatchResult where
  Match m1 <> Match m2 = Match (IntMap.union m1 m2)
  NoMatch  <> _        = NoMatch
  _        <> NoMatch  = NoMatch
  Blocked  <> _        = Blocked
  _        <> Blocked  = Blocked

instance Monoid MatchResult where
  mempty = Match IntMap.empty

matchPattern :: Pattern -> Term -> M MatchResult
matchPattern pat t = case pat of
  VarPat i         -> return $ Match (IntMap.singleton i t)
  AxiomPat id args -> whnf t >>= \case
    BlockedMeta _ _  -> return Blocked
    BlockedAxiom _ _ -> return Blocked
    -- TODO: what happens if the arg lengths do not match?
    Axiom h termArgs | h == id && length args == length termArgs ->
      mconcat <$> mapM (uncurry matchPattern) (zip args termArgs)
    _ -> return NoMatch

applyRules :: NameId -> [Term] -> [Rule] -> M Term
applyRules id args []          = return $ Axiom id args
applyRules id args (rule:rest)
  | length (ruleArgs rule) <= length args = do
    result <- mconcat <$> mapM (uncurry matchPattern) (zip (ruleArgs rule) args)
    case result of
      Match vars -> do
        let n          = ruleCtxLength rule
            varTerms   = reverse [vars IntMap.! i | i <- [0..n-1]]
            extraTerms = drop (length (ruleArgs rule)) args
        whnf $ applyTerm (ruleRhs rule) (varTerms ++ extraTerms)
      Blocked    -> return $ BlockedAxiom id args
      NoMatch    -> applyRules id args rest
  | otherwise = applyRules id args rest

-- | Attempts to reduce a term to a weak head normal form.
whnf :: Term -> M Term
whnf t = case t of
  BlockedMeta id args -> do
    -- TODO: path compression?
    lookupState id metaTerms >>= \case
      Nothing -> return t
      Just t' -> whnf (applyTerm t' args)
  BlockedAxiom id args -> do
    rules <- fromMaybe [] <$> lookupState id axiomRules
    applyRules id args rules
  Axiom id args -> do
    rules <- fromMaybe [] <$> lookupState id axiomRules
    applyRules id args rules
  t -> return t

unify :: Ctx -> Type -> Term -> Term -> M Constraint
unify ctx ty t1 t2 = do
  ty' <- whnf ty
  t1' <- whnf t1
  t2' <- whnf t2
  debugFields "unify" $
    [ "ctx"  |: prettyCtx ctx
    , "type" |: prettyTerm ctx ty'
    , "a"    |: prettyTerm ctx t1'
    , "b"    |: prettyTerm ctx t2'
    ]
  case (ty', t1', t2') of
    -- TODO: intersect?
    (_, BlockedMeta m1 _, BlockedMeta m2 _) | m1 == m2 ->
      return $ TermEq ctx ty' t1' t2'

    (_, BlockedMeta m1 args1, BlockedMeta m2 args2) -> flexFlex ctx ty' m1 args1 m2 args2
    (_, BlockedMeta m args, t) -> flexRigid ctx ty' m args t
    (_, t, BlockedMeta m args) -> flexRigid ctx ty' m args t

    (_, BlockedAxiom _ _, _) -> return $ TermEq ctx ty' t1' t2'
    (_, _, BlockedAxiom _ _) -> return $ TermEq ctx ty' t1' t2'

    (_, Var i1 args1, Var i2 args2)
      | i1 == i2 && length args1 == length args2 ->
        unifySpine ctx (ctxLookup ctx i1) (zip args1 args2)
    (_, Axiom n1 args1, Axiom n2 args2)
      | n1 == n2 && length args1 == length args2 -> do
        nty <- getState n1 axiomTypes
        unifySpine ctx nty (zip args1 args2)

    -- Π-types (with η)
    (Pi a b, Lam e1, Lam e2) -> unify (ctx :> a) b e1 e2
    (Pi a b, Lam e, t)       -> unify (ctx :> a) b e (applyTerm (weaken t) [var 0])
    (Pi a b, t, Lam e)       -> unify (ctx :> a) b (applyTerm (weaken t) [var 0]) e

    (Type, Type, Type) -> return $ Solved True
    (Type, Pi a1 b1, Pi a2 b2) -> unifyDependentTypes ctx a1 b1 a2 b2
    (Type, Sigma a1 b1, Sigma a2 b2) -> unifyDependentTypes ctx a1 b1 a2 b2
        
    _ -> return $ Solved False

unifySpine :: Ctx -> Type -> [(Term, Term)] -> M Constraint
unifySpine _ _ [] = return $ Solved True
unifySpine ctx ty ((arg1, arg2):rest) = do
  debugFields "unify spine" $
    [ "ctx"  |: prettyCtx ctx
    , "type" |: prettyTerm ctx ty
    , "arg1" |: prettyTerm ctx arg1
    , "arg2" |: prettyTerm ctx arg2
    ]
  (a, b) <- whnf ty >>= \case
    Pi a b -> return (a, b)
    _      -> error "unifySpine: term is not well-typed"
  -- If B does not depend on A (i.e. this is a non-dependent function type) then
  -- we don't need to guard on the argument constraint.
  case strengthen b of
    Nothing -> guarded (TermEq ctx a arg1 arg2) (SpineEq ctx (instantiate b arg1) rest)
    Just b' -> simplify $ And [TermEq ctx a arg1 arg2, SpineEq ctx b' rest]

-- | Unifies A₁ with A₂, and B₁ with B₂ (over the first equality).
unifyDependentTypes :: Ctx -> Type -> Type -> Type -> Type -> M Constraint
unifyDependentTypes ctx a1 b1 a2 b2 =
  -- If B does not depend on A in one of the types, then we don't have to
  -- wait for A to be checked before checking B.
  case (strengthen b1, strengthen b2) of
    (Nothing , Nothing ) ->
      -- We must have a1 ≡ a2 before b1 ≡ b2 makes sense.
      guarded (TermEq ctx Type a1 a2) (TermEq (ctx :> a1) Type b1 b2)
      -- If b1 does not depend on a1, then we can also treat b1 as belong to
      -- context (ctx :> a2), so we don't have to depend on the first
      -- equality.
    (Just _  , Nothing ) ->
      simplify $ And [TermEq ctx Type a1 a2, TermEq (ctx :> a2) Type b1 b2]
    (Nothing , Just _  ) ->
      -- flipped version of previous case
      simplify $ And [TermEq ctx Type a1 a2, TermEq (ctx :> a1) Type b1 b2]
      -- If neither b1 nor b2 depend on a, then we can check the equality of
      -- the strengthened versions.
    (Just b1', Just b2') ->
      simplify $ And [TermEq ctx Type a1 a2, TermEq ctx Type b1' b2']

-- | Try both ways.
flexFlex :: Ctx -> Type -> MetaId -> [Term] -> MetaId -> [Term] -> M Constraint
flexFlex ctx ty m1 args1 m2 args2 = do
  let t1 = BlockedMeta m1 args1
      t2 = BlockedMeta m2 args2
  solveMeta args1 t2 >>= \case
    Just t2' -> do
      assignMeta m1 t2'
      return $ Solved True
    Nothing -> solveMeta args2 t1 >>= \case
      Just t1' -> do
        assignMeta m2 t1'
        return $ Solved True
      Nothing -> return $ TermEq ctx ty t1 t2

flexRigid :: Ctx -> Type -> MetaId -> [Term] -> Term -> M Constraint
flexRigid ctx ty m args t =
  solveMeta args t >>= \case
    Nothing -> return $ TermEq ctx ty (BlockedMeta m args) t
    Just t' -> do
      assignMeta m t'
      return $ Solved True

-- | Given α args = t, try to find a unique solution for α.
solveMeta :: [Term] -> Term -> M (Maybe Term)
solveMeta args t = runMaybeT $ do
  σ  <- convertMetaArgs args
  t' <- invertVarSubst σ t
  -- TODO: occurs check
  return $ makeLam (length args) t'
  where
    makeLam 0 t' = t'
    makeLam n t' = makeLam (n - 1) (Lam t')

-- A variable substitution, represented as a list of de Bruijn indices. Note
-- that this may seem reversed, since index zero is written on the left for
-- lists but on the right in contexts.
-- TODO: use strict list
type VarSubst = [Int]

-- An analogue of SubstLift. liftVarSubst σ acts like the identity on var 0,
-- and like σ on other vars.
liftVarSubst :: VarSubst -> VarSubst
liftVarSubst σ = 0 : map (+ 1) σ

-- Determine if a series of arguments (to a meta) is a variable substitution.
convertMetaArgs :: [Term] -> MaybeT M VarSubst
convertMetaArgs args = mapM convertMetaArg (reverse args)
  where
    convertMetaArg t = do
      t' <- lift $ whnf t
      case t' of
        Var i [] -> return i
        _ -> mzero

-- invertVarSubst σ t tries to find a unique term u such that u[σ] = t.
invertVarSubst :: VarSubst -> Term -> MaybeT M Term
invertVarSubst σ t = do
  t' <- lift $ whnf t
  case t' of
    BlockedMeta m args -> BlockedMeta m <$> mapM (invertVarSubst σ) args
    BlockedAxiom n args -> BlockedAxiom n <$> mapM (invertVarSubst σ) args
    Axiom n args -> Axiom n <$> mapM (invertVarSubst σ) args
    Var i args -> case elemIndices i σ of
        [i'] -> Var i' <$> mapM (invertVarSubst σ) args
        _ -> mzero
    Lam b -> Lam <$> invertVarSubst (liftVarSubst σ) b
    Type -> return Type
    Pi a b -> Pi <$> invertVarSubst σ a <*> invertVarSubst (liftVarSubst σ) b
    Sigma a b -> Sigma <$> invertVarSubst σ a <*> invertVarSubst (liftVarSubst σ) b
