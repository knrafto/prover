module TypeCheck where

import           Control.Monad.State
import           Data.List
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict as Map
import           Data.Text                      ( Text )
import qualified Data.Text as Text

import qualified Syntax

-- This description of type theory is based on §A.2 in the HoTT book.

-- A context is roughly a list of types. It represents a "tower" of dependent
-- types. We leave variables unnamed, and use De Bruijn indexes.
data Context
    -- () ctx
    = Empty
    -- If Γ ⊢ A : Type, then (Γ, A) ctx
    | Extend Term

-- A term represents a derivation of a judgement Γ ⊢ a : A.
data Term
    -- Γ ⊢ Type : Type
    = Universe Context
    -- An assumption () ⊢ a : A.
    | Assume Term Text
    -- If Γ ⊢ A : Type and Γ ⊢ b : B, then (Γ, A) ⊢ ↑b : ↑B
    -- We use this instead of traditional de Bruijn indices, similar to the
    -- 'bound' library for Haskell.
    | Weaken Term Term
    -- If Γ ⊢ A : Type, then (Γ, A) ⊢ v : ↑A
    -- Corresponds to de Bruijn index 0.
    | Var Term
    -- If Γ ⊢ A : Type and (Γ, A) ⊢ B : Type, then Γ ⊢ Π A B : Type
    | Pi Term Term
    -- If Γ ⊢ A : Type and (Γ, A) ⊢ b : B then Γ ⊢ λ A b : Π A B
    | Lam Term Term
    -- If Γ ⊢ A : Type and (Γ, A) ⊢ B : Type and Γ ⊢ f : Π A B and Γ ⊢ a : A,
    -- then Γ ⊢ f(a) : B[a]
    | App Term Term Term Term 
    -- If Γ ⊢ A : Type and (Γ, A) ⊢ B : Type, then Γ ⊢ Σ A B : Type
    | Sigma Term Term

-- Extracts the context from a term.
context :: Term -> Context
context (Universe _Γ) = _Γ
context (Assume _ _) = Empty
context (Weaken _A _) = Extend _A
context (Var _A) = Extend _A
context (Pi _A _B) = context _A
context (Lam _A _) = context _A
context (App _A _ _ _) = context _A
context (Sigma _A _B) = context _A

-- Extracts the type of a term.
termType :: Term -> Term
termType (Universe _Γ) = Universe _Γ
termType (Assume _A _) = _A
termType (Weaken _A b) = Weaken _A (termType b)
termType (Var _A) = Weaken _A _A
termType (Pi _A _B) = Universe (context _A)
termType (Lam _A b) = Pi _A (termType b)
termType (App _ _B _ a) = subst a _B
termType (Sigma _A _B) = Universe (context _A)

-- If Γ ⊢ a : A and (Γ, A) ⊢ b : B, then Γ ⊢ b[a] : B[a].
subst :: Term -> Term -> Term
subst a = subst' (SubstTerm a)

-- Auxiliary type to help with `subst` below. An element represents a
-- substitution of context Δ → Γ. Given a substitution σ : Δ → Γ, we get a
-- contravariant action on terms σ* : Term Γ A → Term Δ (σ* A), implemented
-- by `subst'` below.
data Subst
    -- Given Γ ⊢ a : A, we get a substitution Γ → (Γ, A) 
    = SubstTerm Term
    -- Given a substitution σ : Δ → Γ, we get a substitution
    -- (Δ, σ* A) → (Γ, A).
    | SubstExtend Subst Term

substDomain :: Subst -> Context
substDomain (SubstTerm t) = context t
substDomain (SubstExtend σ _A) = Extend (subst' σ _A)

subst' :: Subst -> Term -> Term
subst' σ (Universe _) = Universe (substDomain σ)
subst' _ (Assume _ _) = error "subst': Assume has empty context"
subst' (SubstTerm _) (Weaken _ b) = b
subst' (SubstExtend σ _) (Weaken _A b) = Weaken (subst' σ _A) (subst' σ b)
subst' (SubstTerm t) (Var _) = t
subst' (SubstExtend σ _) (Var _A) = Var (subst' σ _A)
subst' σ (Pi _A _B) = Pi (subst' σ _A) (subst' (SubstExtend σ _A) _B)
subst' σ (Lam _A b) = Lam (subst' σ _A) (subst' (SubstExtend σ _A) b)
subst' σ (App _A _B f a) = App (subst' σ _A) (subst' (SubstExtend σ _A) _B) (subst' σ f) (subst' σ a)
subst' σ (Sigma _A _B) = Sigma (subst' σ _A) (subst' (SubstExtend σ _A) _B)

-- Rules for definitional equality:
-- * Weakening commutes with Pi, Lam, App, and Sigma
-- * β-conversion
-- * η-conversion
normalize :: Term -> Term
normalize = _

data TcState = TcState
    -- Global definitions, and their values.
    { tcDefinitions :: Map Text Term
    -- Global assumptions, and their types.
    , tcAssumptions :: Map Text Term
    }

initialState :: TcState
initialState = TcState { tcDefinitions = Map.empty, tcAssumptions = Map.empty }

type TcM a = StateT TcState IO a

typeCheck :: [Syntax.Statement] -> IO TcState
typeCheck statements = execStateT (mapM_ typeCheckStatement statements) initialState

typeCheckStatement :: Syntax.Statement -> TcM ()
typeCheckStatement (Syntax.Define name body) = do
    body' <- normalize <$> typeCheckExpr Empty [] body
    modify $ \s -> s { tcDefinitions = Map.insert name body' (tcDefinitions s) }
typeCheckStatement (Syntax.Assume name ty) = do
    ty' <- normalize <$> typeCheckExpr Empty [] ty
    modify $ \s -> s { tcAssumptions = Map.insert name ty' (tcAssumptions s) }
typeCheckStatement (Syntax.Prove _) = fail ":prove not implemented"

typeCheckExpr :: Context -> [Text] -> Syntax.Expr -> TcM Term
typeCheckExpr _Γ names (Syntax.Var name) = do
    definitions <- gets tcDefinitions
    assumptions <- gets tcAssumptions
    case () of
        _ | Just i <- elemIndex name names ->
                return _
          | Just body <- Map.lookup name definitions ->
                return _
          | Just ty <- Map.lookup name assumptions ->
                return _
          | otherwise ->
                fail $ "unbound name: " ++ Text.unpack name
typeCheckExpr _Γ _ Syntax.Universe = return (Universe _Γ)
typeCheckExpr _Γ names (Syntax.Pi name _A _B) = do
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    _B' <- typeCheckExpr (Extend _A') (name : names) _B
    checkIsType _B'
    return (Pi _A' _B')
typeCheckExpr _Γ names (Syntax.Arrow _A _B) = do
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    _B' <- typeCheckExpr _Γ names _B
    checkIsType _B'
    return (Pi _A' (Weaken _A' _B'))
typeCheckExpr _Γ names (Syntax.Lam name _A b) = do
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    b' <- typeCheckExpr (Extend _A') (name : names) b
    return (Lam _A' b')
typeCheckExpr _Γ names (Syntax.App f args) = do
    f' <- typeCheckExpr _Γ names f
    args' <- mapM (typeCheckExpr _Γ names) args
    typeCheckApp f' args'
typeCheckExpr _Γ names (Syntax.Sigma name _A _B) = do
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    _B' <- typeCheckExpr (Extend _A') (name : names) _B
    checkIsType _B'
    return (Sigma _A' _B')

checkIsType :: Term -> TcM ()
checkIsType = _
{-
checkIsType t = case normalize (termType t) of
    Universe _ -> return ()
    _ -> fail "not a type"
-}

typeCheckApp :: Term -> [Term] -> TcM Term
typeCheckApp = _
{-
typeCheckApp f [] = return f
typeCheckApp f (arg : args) = do
    a <- case normalize (termType f) of
        Pi a _ -> return a
        _ -> fail $ "not a Π-type"
    unless (judgmentallyEqual a (termType arg)) $
        fail "argument type of function does not match type of argument"
    typeCheckApp (App f arg) args
-}