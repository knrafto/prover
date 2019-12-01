module Term where

import Data.Text (Text)

newtype MetaId = MetaId Int
    deriving (Eq, Ord, Show)

-- Core term representation. Terms are always well-typed.
data Term
    = Meta {-# UNPACK #-} !MetaId [Term]
    | Var {-# UNPACK #-} !Int [Term]
    | Assumption !Text [Term]
    | Lam !Term
    | Universe
    | Pi !Type !Type
    deriving (Eq, Show)

type Type = Term

-- A context.
data Ctx
    = EmptyCtx
    | ExtendCtx !Ctx !Type

instance Show Ctx where
    showsPrec _ EmptyCtx = showString "()"
    showsPrec _ (ExtendCtx ctx ty) = showChar '(' . go ctx . shows ty . showChar ')'
      where
        go EmptyCtx = id
        go (ExtendCtx ctx' ty') = go ctx' . shows ty' . showString ", "

-- Returns the number of variables in a context.
ctxLength :: Ctx -> Int
ctxLength EmptyCtx = 0
ctxLength (ExtendCtx ctx _) = 1 + ctxLength ctx

-- Construct a Π-type out of a context ending with the given type.
ctxPi :: Ctx -> Type -> Type
ctxPi EmptyCtx t = t
ctxPi (ExtendCtx ctx ty) t = ctxPi ctx (Pi ty t)

-- Construct a lambda out of a context with the given body.
ctxLam :: Ctx -> Term -> Term
ctxLam EmptyCtx t = t
ctxLam (ExtendCtx ctx _) t = ctxLam ctx (Lam t)

-- Returns all the bound variables of a context, in the same order as ctxPi
-- e.g. v₃ v₂ v₁ v₀.
ctxVars :: Ctx -> [Term]
ctxVars = reverse . go 0
  where
    go _ EmptyCtx = []
    go i (ExtendCtx ctx _) = Var i [] : go (i + 1) ctx

ctxVarType :: Ctx -> Int -> Type
ctxVarType EmptyCtx _ = error "ctxVarType: empty context"
ctxVarType (ExtendCtx _ ty) 0 = weaken ty
ctxVarType (ExtendCtx ctx _) i = weaken (ctxVarType ctx (i - 1))

-- Substitutions.
data Subst
    = SubstWeaken {-# UNPACK #-} !Int
    | SubstLift !Subst
    | SubstTerm !Term

-- Perform a substitution.
applySubst :: Subst -> Term -> Term
applySubst subst t = case t of
    Meta m args -> Meta m (map (applySubst subst) args)
    Var i args -> app (applySubstToVar subst i) args
    Assumption n args -> Assumption n (map (applySubst subst) args)
    Lam b -> Lam (applySubst (SubstLift subst) b)
    Universe -> t
    Pi _A _B -> Pi (applySubst subst _A) (applySubst (SubstLift subst) _B)
  where
    applySubstToVar (SubstWeaken k) i = Var (i + k) []
    applySubstToVar (SubstLift _) 0 = Var 0 []
    applySubstToVar (SubstLift subst') i = weaken (applySubstToVar subst' (i - 1))
    applySubstToVar (SubstTerm a) 0 = a
    applySubstToVar (SubstTerm _) i = Var (i - 1) []

-- Weaken a term.
weaken :: Term -> Term
weaken = applySubst (SubstWeaken 1)

-- Weaken a closed term into a context.
weakenGlobal :: Ctx -> Term -> Term
weakenGlobal ctx = applySubst (SubstWeaken (ctxLength ctx))

-- Substitute for the first bound variable.
instantiate :: Term -> Term -> Term
instantiate t a = applySubst (SubstTerm a) t

-- Apply a term to args.
app :: Term -> [Term] -> Term
app t [] = t
app t args@(arg : rest) = case t of
    Meta i args0 -> Meta i (args0 ++ args)
    Var i args0 -> Var i (args0 ++ args)
    Assumption i args0 -> Assumption i (args0 ++ args)
    Lam b -> app (instantiate b arg) rest
    _ -> error "app: cannot apply type of arguments"
