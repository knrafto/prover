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
data Term
  -- | A metavariable under a substitution applied to args.
  = Meta !MetaId Subst [Term]
  -- | A neutral axiom applied to args.
  | Axiom !NameId [Term]
  -- | A definition applied to args.
  | Def !NameId [Term]
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
  deriving (Eq, Show)

type Type = Term

-- | A strict list where new things go on the right.
data RList a
  = Empty
  | !(RList a) :> !a
  deriving (Eq, Show, Functor, Foldable, Traversable)

rlength :: RList a -> Int
rlength Empty = 0
rlength (l :> _) = length l + 1

rindex :: RList a -> Int -> a
rindex Empty _    = error "rindex"
rindex (_ :> a) 0 = a
rindex (l :> _) i = rindex l (i - 1)

-- | A context for a term.
type Ctx = RList Type

-- | A substitution between contexts, represented as a list of terms. A
-- substitution from Δ to the empty context is an empty list of terms; a
-- substitution from Δ to (Γ, A) is a substitution σ : Δ → Γ and a term in
-- context Δ of type A[σ].
type Subst = RList Term

-- | Construct a bound variable.
var :: Int -> Term
var i = Var i []

-- | Lift a term in context Γ to a term of in the extended context Γ, A
-- (essentially adding an unused 0th variable).
weaken :: Term -> Term
weaken = weakenBy 1

-- | Lift a term in context Γ to a term of in the extended context by k
-- variables.
weakenBy :: Int -> Term -> Term
weakenBy k = go 0
  where
  -- Add the ith through (i + k)th variable
  go !i = \case
    Meta m subst args -> Meta m (fmap (go i) subst) (map (go i) args)
    Axiom n args      -> Axiom n (map (go i) args)
    Def n args        -> Def n (map (go i) args)
    Var j args
      | j < i         -> Var j (map (go i) args)
      | otherwise     -> Var (j + k) (map (go i) args)
    Lam b             -> Lam (go (i + 1) b)
    Pair a b          -> Pair (go i a) (go i b)
    Type              -> Type
    Pi a b            -> Pi (go i a) (go (i + 1) b)
    Sigma a b         -> Sigma (go i a) (go (i + 1) b)

-- | Try to find a term that weakens to a given term (in other words, partially
-- invert weaken).
strengthen :: Term -> Maybe Term
strengthen = go 0
  where
  -- Remove the ith variable
  go i = \case
    Meta m subst args -> Meta m <$> traverse (go i) subst <*> traverse (go i) args
    Axiom n args      -> Axiom n <$> traverse (go i) args
    Def n args        -> Def n <$> traverse (go i) args
    Var j args
      | j < i         -> Var j <$> traverse (go i) args
      | j == i        -> Nothing
      | otherwise     -> Var (j - 1) <$> traverse (go i) args
    Lam b             -> Lam <$> go (i + 1) b
    Pair a b          -> Pair <$> go i a <*> go i b
    Type              -> return Type
    Pi a b            -> Pi <$> go i a <*> go (i + 1) b
    Sigma a b         -> Sigma <$> go i a <*> go (i + 1) b

-- | Given a term Γ, A ⊢ t : B and Γ ⊢ a : A, form the term Γ ⊢ t[⟨a⟩] : B[⟨a⟩]
instantiate :: Term -> Term -> Term
instantiate t a = go 0 t
  where
  -- Replace the ith variable with a
  go !i = \case
    Meta m subst args -> Meta m (fmap (go i) subst) (map (go i) args)
    Axiom n args      -> Axiom n (map (go i) args)
    Def n args        -> Def n (map (go i) args)
    Var j args
      | j < i         -> Var j (map (go i) args)
      | j == i        -> applyArgs (weakenBy i a) (map (go i) args)
      | otherwise     -> Var (j - 1) (map (go i) args)
    Lam b             -> Lam (go (i + 1) b)
    Pair a b          -> Pair (go i a) (go i b)
    Type              -> Type
    Pi a b            -> Pi (go i a) (go (i + 1) b)
    Sigma a b         -> Sigma (go i a) (go (i + 1) b)

-- | Apply a term to arguments.
applyArgs :: Term -> [Term] -> Term
applyArgs t [] = t
applyArgs t args@(arg:rest) = case t of
  Meta m subst args'  -> Meta m subst (args' ++ args)
  Axiom n args' -> Axiom n (args' ++ args)
  Def n args'   -> Def n (args' ++ args)
  Var v args'   -> Var v (args' ++ args)
  Lam b         -> applyArgs (instantiate b arg) rest
  _             -> error "applyArgs"

-- | The number of variables in a context.
ctxLength :: Ctx -> Int
ctxLength = rlength

-- | Get the type of a variable in a context.
ctxLookup :: Ctx -> Var -> Type
ctxLookup ctx i = weakenBy (i + 1) (rindex ctx i)

-- | Construct a Π-type out of a context ending with the given type.
ctxPi :: Ctx -> Type -> Type
ctxPi Empty t = t
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
    go _ Empty = []
    go i (ctx :> _) = var i : go (i + 1) ctx
