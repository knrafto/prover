-- | The syntax of the raw type theory.
module Prover.Syntax.Internal where

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

-- | The head of a neutral term.
data Head
  -- | A local variable (as a de Bruijn index).
  = Var !Var
  -- | A defined name.
  | Def !NameId
  -- | An assumed name.
  | Axiom !NameId
  -- | A metavariable.
  | Meta !MetaId
  deriving (Show)

-- | A term in some context of some type. Terms are kept in
-- almost-but-not-quite-normal form with variables represented by de Bruijn
-- indices. The term can only be reduced by substituting for the head of a
-- neutral term.
--
-- A useful property of this representation that we can (ab)use is that a closed
-- term can be used in any context without explicitly applying a substitution.
data Term
  -- | A neutral term application.
  = App !Head [Term]
  -- | A universe.
  | Type
  -- | A Π-type.
  | Pi Term Term
  -- | A lambda function.
  | Lam Term
  deriving (Show)

type Type = Term

-- | A context for a term.
data Ctx
  = C0
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
var i = App (Var i) []

-- | Apply a term to more terms.
applyTerm :: Term -> [Term] -> Term
applyTerm t [] = t
applyTerm t args@(arg:rest) = case t of
  App h args' -> App h (args' ++ args)
  Lam b       -> applyTerm (instantiate b arg) rest
  _           -> error "applyTerm"

lookupVar :: Subst -> Var -> Term
lookupVar (SubstWeaken k)    i = var (i + k)
lookupVar (SubstLift _)      0 = var 0
lookupVar (SubstLift subst') i = weaken (lookupVar subst' (i - 1))
lookupVar (SubstTerm t)      0 = t
lookupVar (SubstTerm _)      i = var (i - 1)

applySubst :: Subst -> Term -> Term
applySubst subst t = case t of
  App (Var v) args -> applyTerm (lookupVar subst v) (map (applySubst subst) args)
  -- All other heads are closed.
  App h       args -> App h (map (applySubst subst) args)
  Type             -> Type
  Pi a b           -> Pi (applySubst subst a) (applySubst (SubstLift subst) b)
  Lam b            -> Lam (applySubst (SubstLift subst) b)

-- TODO: comment
weaken :: Term -> Term
weaken a = applySubst (SubstWeaken 1) a

-- TODO: comment
instantiate :: Term -> Term -> Term
instantiate a t = applySubst (SubstTerm t) a

-- | The number of variables in a context.
ctxLength :: Ctx -> Int
ctxLength C0         = 0
ctxLength (ctx :> _) = 1 + ctxLength ctx

-- | Get the type of a variable in a context.
ctxLookup :: Ctx -> Var -> Type
ctxLookup C0          _ = error "ctxLookup: empty context"
ctxLookup (_   :> ty) 0 = weaken ty
ctxLookup (ctx :> _ ) i = weaken (ctxLookup ctx (i - 1))

-- | Construct a Π-type out of a context ending with the given type.
ctxPi :: Ctx -> Type -> Type
ctxPi C0          t = t
ctxPi (ctx :> ty) t = ctxPi ctx (Pi ty t)

-- | Construct a lambda out of a context with the given body.
ctxLam :: Ctx -> Term -> Term
ctxLam C0         t = t
ctxLam (ctx :> _) t = ctxLam ctx (Lam t)

-- | Returns all the bound variables of a context, in the same order as ctxPi
-- e.g. v₃ v₂ v₁ v₀.
ctxVars :: Ctx -> [Term]
ctxVars = reverse . go 0
  where
    go _ C0         = []
    go i (ctx :> _) = var i : go (i + 1) ctx
