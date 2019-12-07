{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Term where

import Data.Hashable
import Data.Text (Text)
import qualified Data.Text as Text

-- TODO: move to util module
subscript :: String -> Int -> String
subscript name c = name ++ map toSubscriptChar (show c)
  where
    toSubscriptChar = \case
        '0' -> '₀'
        '1' -> '₁'
        '2' -> '₂'
        '3' -> '₃'
        '4' -> '₄'
        '5' -> '₅'
        '6' -> '₆'
        '7' -> '₇'
        '8' -> '₈'
        '9' -> '₉'
        _   -> error "subscript: not a digit"

newtype MetaId = MetaId Int
    deriving (Eq, Ord, Hashable)

instance Show MetaId where
    show (MetaId i) = subscript "α" i

-- Contexts.
data Ctx
    = C0
    | !Ctx :> !Type

instance Show Ctx where
    showsPrec _ C0 = showString "()"
    showsPrec _ (ctx :> ty) = showChar '(' . go ctx . shows ty . showChar ')'
      where
        go C0 = id
        go (ctx' :> ty') = go ctx' . shows ty' . showString ", "

-- Core term representation. Terms are always well-typed.
-- TODO: make lists strict
-- Closed terms (i.e. terms in the empty context) can be lifted "for free":
-- weakening them requires no changes to the term structure.
data Term
    = Meta {-# UNPACK #-} !MetaId [Term]
    | Var {-# UNPACK #-} !Int [Term]
    | Assumption !Text [Term]
    | Lam !Term
    | Universe
    | Pi !Type !Type
    deriving (Eq)

instance Show Term where
    showsPrec d = \case
        Meta m args -> showApp (show m) args
        Var i args -> showApp (subscript "v" i) args
        Assumption t args -> showApp (Text.unpack t) args
        Lam t -> showParen (d > appPrec) $
            showString "λ " . showsPrec (appPrec + 1) t
        Universe -> showString "Type"
        Pi a b -> showParen (d > appPrec) $
            showString "Π " . showsPrec (appPrec + 1) a .
            showString " " . showsPrec (appPrec + 1) b
      where
        appPrec = 10

        showApp f [] = showString f
        showApp f args = showParen (d > appPrec) $
            showString f . showArgs args

        showArgs [] = id
        showArgs (arg:args) =
            showString " " . showsPrec (appPrec + 1) arg . showArgs args

-- Types are terms of type Universe.
type Type = Term

-- Substitutions.
data Subst
    = SubstWeaken {-# UNPACK #-} !Int
    | SubstLift !Subst
    | SubstTerm !Term

-- Returns the number of variables in a context.
ctxLength :: Ctx -> Int
ctxLength C0 = 0
ctxLength (ctx :> _) = 1 + ctxLength ctx

-- Construct a Π-type out of a context ending with the given type.
ctxPi :: Ctx -> Type -> Type
ctxPi C0 t = t
ctxPi (ctx :> ty) t = ctxPi ctx (Pi ty t)

-- Construct a lambda out of a context with the given body.
ctxLam :: Ctx -> Term -> Term
ctxLam C0 t = t
ctxLam (ctx :> _) t = ctxLam ctx (Lam t)

-- Returns all the bound variables of a context, in the same order as ctxPi
-- e.g. v₃ v₂ v₁ v₀.
ctxVars :: Ctx -> [Term]
ctxVars = reverse . go 0
  where
    go _ C0 = []
    go i (ctx :> _) = Var i [] : go (i + 1) ctx

ctxVarType :: Ctx -> Int -> Type
ctxVarType C0 _ = error "ctxVarType: empty context"
ctxVarType (_ :> ty) 0 = weaken ty
ctxVarType (ctx :> _) i = weaken (ctxVarType ctx (i - 1))

-- Perform a substitution.
applySubst :: Subst -> Term -> Term
applySubst subst t = case t of
    Meta m args -> Meta m (map (applySubst subst) args)
    Var i args -> app (applySubstToVar subst i) (map (applySubst subst) args)
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
    _ -> error ("app: cannot apply " ++ show t)
