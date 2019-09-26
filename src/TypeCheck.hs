module TypeCheck where

import           Control.Monad.State
import           Data.Text                      ( Text )

import qualified Syntax

-- This description of type theory is based on §A.2 in the HoTT book.

-- A context is roughly a list of variables. It represents a "tower" of
-- dependent types. We leave variables unnamed, and use De Bruijn indexes.
-- In this representation, the "outermost" type has index 0.
newtype Context = Context [Term]
    deriving (Eq, Show)

-- The empty context.
emptyContext :: Context
emptyContext = Context []

-- The "variable" rule; if Γ ⊢ A : Type, then we may form the context (Γ, A).
extend :: Context -> Term -> Context
extend (Context ts) t = Context (t : ts)

contextLength :: Context -> Int
contextLength (Context ts) = length ts

contextLookup :: Context -> Int -> Term
contextLookup (Context ts) i = ts !! i 

-- A term represents a derivation of a judgment Γ ⊢ a : A.
-- Equality represents syntactic equality (not judgmental equality)
data Term
    -- Γ ⊢ x_i : A_i
    = Var Context !Int
    -- Γ ⊢ Type : Type
    | Universe Context
    -- Γ ⊢ a : A
    | Assume Context Text Term
    -- If Γ ⊢ A : Type and Γ, x : A ⊢ B : Type then Γ ⊢ Π (x : A). B : Type
    | Pi Term Term
    -- If Γ ⊢ A : Type and Γ, x : A ⊢ b : B then Γ ⊢ λ (x : A). b : Π (x : A). B
    | Lam Term Term
    -- If Γ ⊢ f : Π (x : A). B and Γ ⊢ a : A then Γ ⊢ f(a) : B[a/x]
    | App Term Term 
    -- If Γ ⊢ A : Type and Γ, x : A ⊢ B : Type then Γ ⊢ Π (x : A). B : Type
    | Sigma Term Term
    deriving (Eq, Show)

-- Extracts the context from a term.
domain :: Term -> Context
domain (Var ctx _) = ctx
domain (Universe ctx) = ctx
domain (Assume ctx _ _) = ctx
-- TODO: store context in the term itself?
domain (Pi a b) = domain a
domain (Lam a b) = domain a
domain (App f x) = domain f
domain (Sigma a b) = domain a

-- If Γ, Θ ⊢ a : A, then Γ, Δ, Θ ⊢ a : A.
-- The first argument is the new context Γ, Δ, Θ; the second is the length of Θ.
weaken :: Context -> Int -> Term -> Term
weaken ctx k (Var ctx' i)
    | i < k = Var ctx i
    | otherwise = Var ctx (i + contextLength ctx - contextLength ctx')
weaken ctx k (Universe _) = Universe ctx
weaken ctx k (Assume _ n a) = Assume ctx n (weaken ctx k a)
weaken ctx k (Pi a b) =
    let a' = weaken ctx k a
        b' = weaken (extend ctx a') (k + 1) b
    in Pi a' b'
weaken ctx k (Lam a b) =
    let a' = weaken ctx k a
        b' = weaken (extend ctx a') (k + 1) b
    in Lam a' b'
weaken ctx k (App f x) = App (weaken ctx k f) (weaken ctx k x)
weaken ctx k (Sigma a b) =
    let a' = weaken ctx k a
        b' = weaken (extend ctx a') (k + 1) b
    in Pi a' b'

-- If Γ ⊢ a : A and Γ, x : A, Δ ⊢ b : B, then Γ, Δ ⊢ b[a/x] : B[a/x].
-- The first argument is the new context Γ, Δ.
subst :: Context -> Term -> Term -> Term
subst ctx e (Var ctx' i)
    | i < contextLength ctx - contextLength ctx' = Var ctx i
    | i == contextLength ctx - contextLength ctx' = weaken ctx 0 e
    | otherwise = Var ctx (i - 1)
subst ctx e (Universe _) = Universe ctx
subst ctx e (Assume _ n t) = Assume ctx n (subst ctx e t)
subst ctx e (Pi a b) =
        let a' = subst ctx e a
            b' = subst (extend ctx a') e b
        in Pi a' b'
subst ctx e (Lam a b) =
    let a' = subst ctx e a
        b' = subst (extend ctx a') e b
    in Lam a' b'
subst ctx e (App f x) = App (subst ctx e f) (subst ctx e x)
subst ctx e (Sigma a b) =
    let a' = subst ctx e a
        b' = subst (extend ctx a') e b
    in Sigma a' b'

-- From the judgment Γ ⊢ a : A, it is derivable that Γ ⊢ A : Type.
termType :: Term -> Term
termType (Var ctx i) = weaken ctx 0 (contextLookup ctx i)
termType t@(Universe ctx) = t
termType (Assume _ _ t) = t
termType t@(Pi a b) = Universe (domain t)
termType (Lam a b) = Pi a (termType b)
termType t@(App f x) = case termType f of
    Pi a b -> subst (domain x) x b
    _ -> error $ "termType: type of function is not a Π-type" ++ show t
termType t@(Sigma a b) = Universe (domain t)

-- Reduces each term to a normal form. The only judgemental equality is β-reduction.
-- TODO: do contexts have to be normalized?
normalize :: Term -> Term
normalize t@(Var _ _) = t
normalize t@(Universe _) = t
normalize (Assume ctx n a) = Assume ctx n (normalize a)
normalize (Pi a b) = Pi (normalize a) (normalize b)
normalize (Lam a b) = Lam (normalize a) (normalize b)
normalize (App f x) = case normalize f of
    Lam a b -> normalize (subst (domain x) (normalize x) b)
    f' -> App f' (normalize x)
normalize (Sigma a b) = Sigma (normalize a) (normalize b)

-- Decides judgmental equality.
equal :: Term -> Term -> Bool
equal t1 t2 = normalize t1 == normalize t2