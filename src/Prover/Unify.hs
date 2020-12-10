module Prover.Unify where

import Control.Monad
import Data.Maybe

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap

import Prover.Monad
import Prover.Pattern
import Prover.Term

-- TODO: Restructure unification algorithm to get rid of this.
type UnifyM = StateT UnificationProblem M

-- | Try to "simplify" a unification problem, returning a new unification
-- problem whose solutions are in 1-to-1 correspondence with solution to the
-- original problem. All metavariables in the original problem will appear in
-- the simplified problem. Solved constraints will be removed, but unsolved or
-- false constraints will remain.
simplifyProblem :: UnificationProblem -> M UnificationProblem
simplifyProblem problem = do
  (eqs', problem') <- runStateT (solveEquations (problemConstraints problem)) problem
  return problem' { problemConstraints = eqs' }

-- | Try to solve all equations.
solveEquations :: HashMap EquationId Constraint -> UnifyM (HashMap EquationId Constraint)
solveEquations eqs = do
  -- Loop until no more additional metas get solved
  solvedBefore <- gets (HashMap.size . problemMetaTerms)
  eqs' <- HashMap.filter (not . isSolved) <$> mapM simplify eqs
  solvedAfter <- gets (HashMap.size . problemMetaTerms)
  if solvedBefore == solvedAfter then return eqs' else solveEquations eqs'

-- | Determine if a constraint is solved.
isSolved :: Constraint -> Bool
isSolved = \case
  Solved -> True
  _ -> False

-- | Determine if a constraint is inconsistent.
isInconsistent :: Constraint -> Bool
isInconsistent = \case
  Inconsistent -> True
  _ -> False

-- | Simplify a constraint as much as possible. The resulting constraint should
-- not be able to be simplified more, except if a meta is instantiated.
simplify :: Constraint -> UnifyM Constraint
simplify = \case
  Solved            -> return Solved
  Inconsistent      -> return Inconsistent
  TermEq ctx ty a b -> unify ctx ty a b
  SpineEq ctx ty ts -> unifySpine ctx ty ts
  And cs            -> simplifyAnd <$> mapM simplify cs
  ExactlyOne cs     -> simplifyExactlyOne <$> mapM simplify cs
  Guarded guard c   -> guarded guard c

simplifyAnd :: [Constraint] -> Constraint
simplifyAnd cs = case concat <$> traverse clauses cs of
  Nothing  -> Inconsistent
  Just []  -> Solved
  Just [c] -> c
  Just cs  -> And cs
  where
    clauses :: Constraint -> Maybe [Constraint]
    clauses = \case
      Inconsistent  -> Nothing
      Solved        -> Just []
      And cs        -> Just cs
      c             -> Just [c]

simplifyExactlyOne :: [Constraint] -> Constraint
simplifyExactlyOne cs = case filter (not . isInconsistent) cs of
  []  -> Inconsistent
  [c] -> c
  _   -> ExactlyOne cs

guarded :: Constraint -> Constraint -> UnifyM Constraint
guarded guard c = simplify guard >>= \case
  Solved       -> simplify c
  Inconsistent -> return Inconsistent
  guard'       -> return (Guarded guard' c)

-- | Assign a term for a metavariable.
assignMeta :: MetaId -> Term -> UnifyM ()
assignMeta id t =  modify $ \s -> s
  { problemMetaTerms = HashMap.insert id t (problemMetaTerms s) }

-- | The result of trying to reduce a term to weak head normal form.
data WhnfResult
  -- Evaluation is blocked due to unsolved metas. The head can either be an
  -- unsolved meta, or an axiom with rewrite rules.
  = Blocked Term
  -- A term in whnf.
  | Whnf Term
  deriving (Eq, Show)

whnfTerm :: WhnfResult -> Term
whnfTerm = \case
  Blocked t -> t
  Whnf t -> t

-- | The result of a pattern match.
data MatchResult
  -- | The match succeeded, and we can extract terms for context variables.
  = Match (IntMap Term)
  | NoMatch
  | BlockedMatch
  deriving (Eq, Show)

instance Semigroup MatchResult where
  Match m1      <> Match m2     = Match (IntMap.union m1 m2)
  NoMatch       <> _            = NoMatch
  _             <> NoMatch      = NoMatch
  BlockedMatch  <> _            = BlockedMatch
  _             <> BlockedMatch = BlockedMatch

instance Monoid MatchResult where
  mempty = Match IntMap.empty

matchPattern :: Pattern -> Term -> UnifyM MatchResult
matchPattern pat t = case pat of
  VarPat i         -> return $ Match (IntMap.singleton i t)
  AxiomPat id args -> whnf t >>= \case
    Blocked _ -> return BlockedMatch
    -- TODO: what happens if the arg lengths do not match?
    Whnf (Axiom h termArgs) | h == id && length args == length termArgs ->
      mconcat <$> zipWithM matchPattern args termArgs
    _ -> return NoMatch
  PairPat pa pb    -> whnf t >>= \case
    Blocked _ -> return BlockedMatch
    Whnf (Pair a b) -> mappend <$> matchPattern pa a <*> matchPattern pb b
    _ -> return NoMatch

applyRules :: NameId -> [Term] -> [Rule] -> UnifyM WhnfResult
applyRules id args [] = return $ Whnf (Axiom id args)
applyRules id args (rule:rest)
  | length (ruleArgs rule) <= length args = do
    result <- mconcat <$> zipWithM matchPattern (ruleArgs rule) args
    case result of
      Match vars -> do
        let n          = ruleCtxLength rule
            varTerms   = reverse [vars IntMap.! i | i <- [0..n-1]]
            extraTerms = drop (length (ruleArgs rule)) args
        whnf $ applyArgs (ruleRhs rule) (varTerms ++ extraTerms)
      BlockedMatch -> return $ Blocked (Axiom id args)
      NoMatch -> applyRules id args rest
  | otherwise = applyRules id args rest

-- | Attempts to reduce a term to a weak head normal form.
whnf :: Term -> UnifyM WhnfResult
whnf t = case t of
  Meta id subst args -> do
    -- TODO: path compression?
    metaSubst <- gets problemMetaTerms
    case HashMap.lookup id metaSubst of
      Just t' -> whnf (applyArgs (applySubst t' subst) args)
      Nothing -> lift (lookupState id metaTerms) >>= \case
        Just t' -> whnf (applyArgs (applySubst t' subst) args)
        Nothing -> return (Blocked t)
  Axiom id args -> do
    rules <- fromMaybe [] <$> lift (lookupState id axiomRules)
    applyRules id args rules
  Def id args -> do
    t <- lift (getState id defTerms)
    whnf (applyArgs t args)
  t -> return (Whnf t)

unify :: Ctx -> Type -> Term -> Term -> UnifyM Constraint
unify ctx ty t1 t2 = do
  ty' <- whnf ty
  t1' <- whnf t1
  t2' <- whnf t2
  case (ty', t1', t2') of
    -- Test for syntactic equality
    _ | t1' == t2' -> return Solved

    -- TODO: intersect?
    (_, Blocked (Meta m1 _ _), Blocked (Meta m2 _ _)) | m1 == m2 ->
      return $ TermEq ctx (whnfTerm ty') (whnfTerm t1') (whnfTerm t2')

    (_, Blocked (Meta m1 subst1 args1), Blocked (Meta m2 subst2 args2)) ->
      flexFlex ctx (whnfTerm ty') m1 subst1 args1 m2 subst2 args2
    (_, Blocked (Meta m subst args), t) -> flexRigid ctx (whnfTerm ty') m subst args (whnfTerm t)
    (_, t, Blocked (Meta m subst args)) -> flexRigid ctx (whnfTerm ty') m subst args (whnfTerm t)

    (_, Blocked (Axiom _ _), _) -> return $ TermEq ctx (whnfTerm ty') (whnfTerm t1') (whnfTerm t2')
    (_, _, Blocked (Axiom _ _)) -> return $ TermEq ctx (whnfTerm ty') (whnfTerm t1') (whnfTerm t2')

    (_, Whnf (Var i1 args1), Whnf (Var i2 args2))
      | i1 == i2 && length args1 == length args2 ->
        unifySpine ctx (ctxLookup ctx i1) (zip args1 args2)
    (_, Whnf (Axiom n1 args1), Whnf (Axiom n2 args2))
      | n1 == n2 && length args1 == length args2 -> do
        nty <- lift $ getState n1 axiomTypes
        unifySpine ctx nty (zip args1 args2)

    -- Π-types (with η)
    (Whnf (Pi a b), Whnf (Lam e1), Whnf (Lam e2)) -> unify (ctx :> a) b e1 e2
    (Whnf (Pi a b), Whnf (Lam e), t) -> unify (ctx :> a) b e (applyArgs (weaken (whnfTerm t)) [var 0])
    (Whnf (Pi a b), t, Whnf (Lam e)) -> unify (ctx :> a) b (applyArgs (weaken (whnfTerm t)) [var 0]) e

    -- Σ-types (no η)
    (Whnf (Sigma a b), Whnf (Pair a1 b1), Whnf (Pair a2 b2)) -> do
      -- If B does not depend on A (i.e. this is a non-dependent function type) then
      -- we don't need to guard on the argument constraint.
      case strengthen b of
        Nothing -> guarded (TermEq ctx a a1 a2) (TermEq ctx (instantiate b a1) b1 b2)
        Just b' -> simplify $ And [TermEq ctx a a1 a2, TermEq ctx b' b1 b2]

    (Whnf Type, Whnf Type, Whnf Type) -> return Solved
    (Whnf Type, Whnf (Pi a1 b1), Whnf (Pi a2 b2)) -> unifyDependentTypes ctx a1 b1 a2 b2
    (Whnf Type, Whnf (Sigma a1 b1), Whnf (Sigma a2 b2)) -> unifyDependentTypes ctx a1 b1 a2 b2
        
    _ -> return Inconsistent

unifySpine :: Ctx -> Type -> [(Term, Term)] -> UnifyM Constraint
unifySpine _ _ [] = return Solved
unifySpine ctx ty ((arg1, arg2):rest) = do
  (a, b) <- whnf ty >>= \case
    Whnf (Pi a b) -> return (a, b)
    _ -> error "unifySpine: term is not well-typed"
  -- If B does not depend on A (i.e. this is a non-dependent function type) then
  -- we don't need to guard on the argument constraint.
  case strengthen b of
    Nothing -> guarded (TermEq ctx a arg1 arg2) (SpineEq ctx (instantiate b arg1) rest)
    Just b' -> simplify $ And [TermEq ctx a arg1 arg2, SpineEq ctx b' rest]

-- | Unifies A₁ with A₂, and B₁ with B₂ (over the first equality).
unifyDependentTypes :: Ctx -> Type -> Type -> Type -> Type -> UnifyM Constraint
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
flexFlex :: Ctx -> Type -> MetaId -> Subst -> [Term] -> MetaId -> Subst -> [Term] -> UnifyM Constraint
flexFlex ctx ty m1 subst1 args1 m2 subst2 args2 = do
  let t1 = Meta m1 subst1 args1
      t2 = Meta m2 subst2 args2
  solveMeta subst1 args1 t2 >>= \case
    Just t2' -> do
      assignMeta m1 t2'
      return Solved
    Nothing -> solveMeta subst2 args2 t1 >>= \case
      Just t1' -> do
        assignMeta m2 t1'
        return Solved
      Nothing -> return $ TermEq ctx ty t1 t2

flexRigid :: Ctx -> Type -> MetaId -> Subst -> [Term] -> Term -> UnifyM Constraint
flexRigid ctx ty m subst args t =
  solveMeta subst args t >>= \case
    Nothing -> return $ TermEq ctx ty (Meta m subst args) t
    Just t' -> do
      assignMeta m t'
      return Solved

-- | Given α[σ] args = t, try to find a unique solution for α.
solveMeta :: Subst -> [Term] -> Term -> UnifyM (Maybe Term)
solveMeta subst args t = runMaybeT $ do
  varSubst <- mapM extractVar (addArgs subst args)
  t' <- invertVarSubst varSubst t
  -- TODO: occurs check
  return $ makeLam (length args) t'
  where
    addArgs subst [] = subst
    addArgs subst (arg:rest) = addArgs (subst :> arg) rest

    extractVar t = do
      t' <- lift $ whnf t
      case t' of
        Whnf (Var i []) -> return i
        _ -> mzero

type VarSubst = RList Var

liftVarSubst :: VarSubst -> VarSubst
liftVarSubst subst = fmap (+ 1) subst :> 0

-- | Try to find a unique term u such that u[σ] = t.
invertVarSubst :: VarSubst -> Term -> MaybeT UnifyM Term
invertVarSubst subst t = do
  t' <- lift $ whnf t
  case whnfTerm t' of
    Meta m subst' args -> Meta m <$> mapM (invertVarSubst subst) subst' <*> mapM (invertVarSubst subst) args
    Axiom n args -> Axiom n <$> mapM (invertVarSubst subst) args
    Def n args -> Def n <$> mapM (invertVarSubst subst) args
    Var i args -> case relemIndices i subst of
        [i'] -> Var i' <$> mapM (invertVarSubst subst) args
        _ -> mzero
    Lam b -> Lam <$> invertVarSubst (liftVarSubst subst) b
    Pair a b -> Pair <$> invertVarSubst subst a <*> invertVarSubst subst b
    Type -> return Type
    Pi a b -> Pi <$> invertVarSubst subst a <*> invertVarSubst (liftVarSubst subst) b
    Sigma a b -> Sigma <$> invertVarSubst subst a <*> invertVarSubst (liftVarSubst subst) b
