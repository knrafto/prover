-- | Raw type theory.
module Prover.Term where

import Data.Hashable

-- | A de Bruijn index.
type Var = Int

-- | A unique identifier for a thing with a name, used to determine if two names
-- refer to "the same thing", or two different things with the same name.
newtype NameId = NameId Int
  deriving (Eq, Ord, Show, Enum, Hashable)

-- | A unique identifier for a metavariable.
newtype MetaId = MetaId Int
  deriving (Eq, Ord, Show, Enum, Hashable)

-- | A term in some context of some type. Terms are kept in
-- almost-but-not-quite-normal form with variables represented by de Bruijn
-- indices. The term can only be reduced by substituting for the head of a
-- neutral term.
--
-- A useful property of this representation that we can (ab)use is that a closed
-- term can be used in any context without explicitly applying a substitution.
--
-- TODO: having both BlockedAxiom and Axiom is very confusing.
data Term
  -- | A metavariable applied to args.
  = BlockedMeta !MetaId [Term]
  -- | An axiom applied to args that may be reduced when more metas are solved.
  | BlockedAxiom !NameId [Term]
  -- | A neutral axiom applied to args.
  | Axiom !NameId [Term]
  -- | A de Bruijn variable applied to args.
  | Var !Var [Term]
  -- | A lambda function.
  | Lam Term
  -- | A dependent pair.
  | Pair Term Term
  -- | A universe.
  | Type
  -- | A Π-type.
  | Pi Term Term
  -- | A Σ-type.
  | Sigma Term Term
  deriving (Show)

type Type = Term

-- | A context for a term.
data Ctx
  = EmptyCtx
  | !Ctx :> Type
  deriving (Show)

-- | Substitutions.
-- TODO: revisit. Add comments with type-theoretic explanations, and add more
-- (e.g. identity, lift from empty context)
data Subst
  = SubstWeaken !Int
  | SubstLift Subst
  | SubstTerm Term
  deriving (Show)

-- | Construct a bound variable.
var :: Int -> Term
var i = Var i []

-- | Apply a term to more terms.
applyTerm :: Term -> [Term] -> Term
applyTerm t [] = t
applyTerm t args@(arg:rest) = case t of
  BlockedMeta m args'   -> BlockedMeta m (args' ++ args)
  BlockedAxiom n args'  -> BlockedAxiom n (args' ++ args)
  Axiom n args'         -> Axiom n (args' ++ args)
  Var v args'           -> Var v (args' ++ args)
  Lam b                 -> applyTerm (instantiate b arg) rest
  _                     -> error "applyTerm"

lookupVar :: Subst -> Var -> Term
lookupVar (SubstWeaken k)    i = var (i + k)
lookupVar (SubstLift _)      0 = var 0
lookupVar (SubstLift subst') i = weaken (lookupVar subst' (i - 1))
lookupVar (SubstTerm t)      0 = t
lookupVar (SubstTerm _)      i = var (i - 1)

applySubst :: Subst -> Term -> Term
applySubst subst = \case
  BlockedMeta m args  -> BlockedMeta m (map (applySubst subst) args)
  BlockedAxiom n args -> BlockedAxiom n (map (applySubst subst) args)
  Axiom n args        -> Axiom n (map (applySubst subst) args)
  Var v args          -> applyTerm (lookupVar subst v) (map (applySubst subst) args)
  Lam b               -> Lam (applySubst (SubstLift subst) b)
  Pair a b            -> Pair (applySubst subst a) (applySubst subst b)
  Type                -> Type
  Pi a b              -> Pi (applySubst subst a) (applySubst (SubstLift subst) b)
  Sigma a b           -> Sigma (applySubst subst a) (applySubst (SubstLift subst) b)

-- TODO: comment
weaken :: Term -> Term
weaken a = applySubst (SubstWeaken 1) a

strengthen :: Term -> Maybe Term
strengthen = go 0
  where
  go :: Int -> Term -> Maybe Term
  go i = \case
    BlockedMeta m args  -> BlockedMeta m <$> traverse (go i) args
    BlockedAxiom n args -> BlockedAxiom n <$> traverse (go i) args
    Axiom n args        -> Axiom n <$> traverse (go i) args
    Var j args
      | j < i           -> Var j <$> traverse (go i) args
      | j == i          -> Nothing
      | otherwise       -> Var (j - 1) <$> traverse (go i) args
    Lam b               -> Lam <$> go (i + 1) b
    Pair a b            -> Pair <$> go i a <*> go i b
    Type                -> return Type
    Pi a b              -> Pi <$> go i a <*> go (i + 1) b
    Sigma a b           -> Sigma <$> go i a <*> go (i + 1) b

-- TODO: comment
instantiate :: Term -> Term -> Term
instantiate a t = applySubst (SubstTerm t) a

-- | The number of variables in a context.
ctxLength :: Ctx -> Int
ctxLength EmptyCtx   = 0
ctxLength (ctx :> _) = 1 + ctxLength ctx

-- | Get the type of a variable in a context.
ctxLookup :: Ctx -> Var -> Type
ctxLookup EmptyCtx    _ = error "ctxLookup: empty context"
ctxLookup (_   :> ty) 0 = weaken ty
ctxLookup (ctx :> _ ) i = weaken (ctxLookup ctx (i - 1))

-- | Construct a Π-type out of a context ending with the given type.
ctxPi :: Ctx -> Type -> Type
ctxPi EmptyCtx    t = t
ctxPi (ctx :> ty) t = ctxPi ctx (Pi ty t)

-- | Add n lambdas to a term.
makeLam :: Int -> Term -> Term
makeLam 0 t = t
makeLam n t = makeLam (n - 1) (Lam t)

-- | Construct a lambda out of a context with the given body.
ctxLam :: Ctx -> Term -> Term
ctxLam ctx = makeLam (ctxLength ctx)

-- | Returns all the bound variables of a context, in the same order as ctxPi
-- e.g. v₃ v₂ v₁ v₀.
ctxVars :: Ctx -> [Term]
ctxVars = reverse . go 0
  where
    go _ EmptyCtx   = []
    go i (ctx :> _) = var i : go (i + 1) ctx
