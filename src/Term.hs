-- This description of type theory is based on:
-- Type Theory in Type Theory using Quotient Inductive Types
-- Thorsten Altenkirch, Ambrus Kaposi
-- http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf

-- ... with some modifications. We don't have a separate "Ty" concept, and
-- we represent variables and substitutions less "categorically".
module Term where

import           Data.Text                      ( Text )
import qualified Data.Text                     as Text

data Context
    -- ∙ is a context
    = Empty
    -- If A : Tm Γ U, then (Γ, A) is a context
    | Extend Term

instance Show Context where
    showsPrec _ Empty = showString "∙"
    showsPrec _ _Γ    = showParen True (go _Γ)
      where
        go Empty       = showString "∙"
        go (Extend _A) = go (context _A) . showString ", " . shows _A

-- A substitution between contexts.
-- TODO: represent "categorically".
data Subst
    -- Given A : Tm Γ U, we get a substitution (Γ , A) → Γ
    = SubstWeaken Term
    -- Given t : Tm Γ A, we get a substitution Γ → (Γ, A) 
    | SubstTerm Term
    -- Given a substitution σ : Δ → Γ, we get a substitution
    -- σ ↑ A : (Δ, A[σ]) → (Γ, A).
    | SubstExtend Subst Term

instance Eq Subst where
    (SubstWeaken _   ) == (SubstWeaken _   ) = True
    (SubstTerm   t1  ) == (SubstTerm   t2  ) = t1 == t2
    (SubstExtend σ1 _) == (SubstExtend σ2 _) = σ1 == σ2
    _                  == _                  = False

instance Show Subst where
    showsPrec _ (SubstWeaken _A  ) = showString "wk"
    showsPrec _ (SubstTerm   t   ) = showString "⟨" . shows t . showString "⟩"
    showsPrec _ (SubstExtend σ _A) = shows σ . showString " ↑ " . shows _A

substDomain :: Subst -> Context
substDomain (SubstWeaken _A  ) = Extend _A
substDomain (SubstTerm   t   ) = context t
substDomain (SubstExtend σ _A) = Extend (Apply σ _A)

substCodomain :: Subst -> Context
substCodomain (SubstWeaken _A  ) = context _A
substCodomain (SubstTerm   t   ) = Extend (termType t)
substCodomain (SubstExtend _ _A) = Extend _A

newtype VarId = VarId Int
    deriving (Eq, Ord, Show)

subscript :: Int -> String
subscript i = map toSubscript (show i)
  where
    toSubscript '0' = '₀'
    toSubscript '1' = '₁'
    toSubscript '2' = '₂'
    toSubscript '3' = '₃'
    toSubscript '4' = '₄'
    toSubscript '5' = '₅'
    toSubscript '6' = '₆'
    toSubscript '7' = '₇'
    toSubscript '8' = '₈'
    toSubscript '9' = '₉'
    toSubscript _   = error "toSubscript: not a digit"

data Var
    -- If A : Tm Γ U, then v₀ : Var (Γ, A) A[wk].
    = VZ Term
    -- If B : Tm Γ U and v : Var Γ B, then vs(v) : Var (Γ, A) B[wk]
    | VS Term Var

instance Eq Var where
    (VZ _   ) == (VZ _   ) = True
    (VS _ v1) == (VS _ v2) = v1 == v2
    _         == _         = False

instance Show Var where
    showsPrec _ v = showString "v" . showString (subscript (deBruijn v))

deBruijn :: Var -> Int
deBruijn (VZ _  ) = 0
deBruijn (VS _ v) = 1 + deBruijn v

fromDeBruijn :: Context -> Int -> Var
fromDeBruijn Empty       _ = error "fromDeBruijn: empty context"
fromDeBruijn (Extend _A) 0 = VZ _A
fromDeBruijn (Extend _A) i = VS _A (fromDeBruijn (context _A) (i - 1))

-- Represents a term in a type and a context. Most functions operating on terms
-- assume that terms' contexts and types are compatible and do not check.
-- The Eq instance checks for syntactic equality, and assumes that both terms
-- have the same context and type.
data Term
    -- U : Tm Γ U
    = Universe Context
    -- A named assumption in Tm Γ A.
    | Assume Text Context Term
    -- A metavar with a context and type.
    | Metavar VarId Context Term
    -- If σ : Subst Δ Γ and t : Tm Γ A, then t[σ] : Tm Δ A[σ].
    | Apply Subst Term
    -- If v : Var Γ A, then var(v) : Tm Γ A
    | Var Var
    -- If A : Tm Γ U and B : Tm (Γ, A) U, then Π(A, B) : Tm Γ U
    | Pi Term Term
    -- If A : Tm Γ U and b : Tm (Γ, A) B, then λ(b) : Tm Γ Π(A, B)
    | Lam Term Term
    -- If A : Tm Γ U and B : Tm (Γ, A) U and f : Tm Γ Π(A, B) and a : Tm Γ A
    -- then app(f, a) : Tm Γ B[⟨a⟩]
    | App Term Term Term Term

instance Eq Term where
    (Universe _    ) == (Universe _    ) = True
    (Assume  n1 _ _) == (Assume  n2 _ _) = n1 == n2
    (Metavar i1 _ _) == (Metavar i2 _ _) = i1 == i2
    (Apply σ1 t1   ) == (Apply σ2 t2   ) = σ1 == σ2 && t1 == t2
    (Var v1        ) == (Var v2        ) = v1 == v2
    (Pi  _A1 _B1   ) == (Pi  _A2 _B2   ) = _A1 == _A2 && _B1 == _B2
    (Lam _   b1    ) == (Lam _   b2    ) = b1 == b2
    (App _ _ f1 a1 ) == (App _ _ f2 a2 ) = f1 == f2 && a1 == a2
    _                == _                = False

instance Show Term where
    showsPrec _ (Universe _  ) = showString "U"
    showsPrec _ (Assume n _ _) = showString (Text.unpack n)
    showsPrec _ (Metavar (VarId i) _ _) =
        showString "α" . showString (subscript i)
    showsPrec _ (Apply σ t) =
        shows t . showString "[" . shows σ . showString "]"
    showsPrec _ (Var v) = shows v
    showsPrec _ (Pi _A _B) =
        showString "Π(" . shows _A . showString ", " . shows _B . showString ")"
    showsPrec _ (Lam _ b) = showString "λ(" . shows b . showString ")"
    showsPrec _ (App _ _ f a) =
        showString "app(" . shows f . showString ", " . shows a . showString ")"

-- Extracts the context from a term.
context :: Term -> Context
context (Universe _Γ   ) = _Γ
context (Assume  _ _Γ _) = _Γ
context (Metavar _ _Γ _) = _Γ
context (Apply σ _     ) = substDomain σ
context (Var v         ) = go v
  where
    go (VZ _A  ) = Extend _A
    go (VS _A _) = Extend _A
context (Pi  _A _    ) = context _A
context (Lam _A _    ) = context _A
context (App _A _ _ _) = context _A

-- Extracts the type of a term.
termType :: Term -> Term
termType (Universe _Γ   ) = Universe _Γ
termType (Assume  _ _ _A) = _A
termType (Metavar _ _ _A) = _A
termType (Apply σ t     ) = Apply σ (termType t)
termType (Var v         ) = go v
  where
    go (VZ _A   ) = Apply (SubstWeaken _A) _A
    go (VS _A v') = Apply (SubstWeaken _A) (go v')
termType (Pi  _A _B   ) = Universe (context _A)
termType (Lam _A b    ) = Pi _A (termType b)
termType (App _ _B _ a) = Apply (SubstTerm a) _B

weakenGlobal :: Context -> Term -> Term
weakenGlobal Empty t = t
weakenGlobal (Extend _A) t =
    Apply (SubstWeaken _A) (weakenGlobal (context _A) t)

-- Checks there are no redexes in the App "spine" of a term.
-- TODO: put this on firm foundation.
isWeakNormal :: Term -> Bool
isWeakNormal (Lam _ _) = True
isWeakNormal t         = isWeakNeutral t
  where
    isWeakNeutral (Universe _   ) = True
    isWeakNeutral (Assume  _ _ _) = True
    isWeakNeutral (Metavar _ _ _) = False
    isWeakNeutral (Apply _ _    ) = False
    isWeakNeutral (Var _        ) = True
    isWeakNeutral (Pi  _ _      ) = True
    isWeakNeutral (Lam _ _      ) = False
    isWeakNeutral (App _ _ f _  ) = isWeakNeutral f

-- Eta-expands a term.
etaExpand :: Term -> Term -> Term -> Term
etaExpand _A _B t = Lam _A (App _A _B (Apply (SubstWeaken _A) t) (Var (VZ _A)))
