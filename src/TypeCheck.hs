module TypeCheck where

import           Control.Monad.State
import           Data.List
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict as Map
import           Data.Text                      ( Text )
import qualified Data.Text as Text

import qualified Syntax

-- This description of type theory is based on:
-- Type Theory in Type Theory using Quotient Inductive Types
-- Thorsten Altenkirch, Ambrus Kaposi
-- http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf

-- ... with some modifications. We don't have a separate "Ty" concept, and
-- we represent variables and substitutions less "categorically".

data Context
    -- ∙ is a context
    = Empty
    -- If A : Tm Γ U, then (Γ, A) is a context
    | Extend Term

-- A substitution between contexts.
data Subst
    -- Given A : Tm Γ U, we get a substitution (Γ , A) → Γ
    = SubstWeaken Term
    -- Given a : Tm Γ A, we get a substitution Γ → (Γ, A) 
    | SubstTerm Term
    -- Given a substitution σ : Δ → Γ, we get a substitution
    -- σ ↑ A : (Δ, A[σ]) → (Γ, A).
    | SubstExtend Subst Term

substDomain :: Subst -> Context
substDomain (SubstWeaken _A) = Extend _A
substDomain (SubstTerm a) = context a
substDomain (SubstExtend σ _A) = Extend (Apply σ _A)

substCodomain :: Subst -> Context
substCodomain (SubstWeaken _A) = context _A
substCodomain (SubstTerm a) = Extend (termType a)
substCodomain (SubstExtend σ _A) = Extend _A

data Term
    -- U : Tm Γ U
    = Universe Context
    -- A named assumption in Tm ∙ A.
    | Assume Term Text
    -- If σ : Subst Δ Γ and t : Tm Γ A, then t[σ] : Tm Δ A[σ].
    | Apply Subst Term
    -- If A : Tm Γ U, then v : Tm (Γ, A) A[wk].
    | Var Term
    -- If A : Tm Γ U and B : Tm (Γ, A) U, then Π A B : Tm Γ U
    | Pi Term Term
    -- If A : Tm Γ U and b : Tm (Γ, A) B, then lam(b) : Tm (Π A B)
    | Lam Term Term
    -- If A : Tm Γ U and B : Tm (Γ, A) U and and f : Tm (Π A B),
    -- then app(f) : Tm (Γ, A) B
    | App Term Term Term 
    -- If A : Tm Γ U and B : Tm (Γ, A) U, then Σ A B : Tm Γ U
    | Sigma Term Term

-- Extracts the context from a term.
context :: Term -> Context
context (Universe _Γ) = _Γ
context (Assume _ _) = Empty
context (Apply σ _) = substDomain σ
context (Var _A) = Extend _A
context (Pi _A _B) = context _A
context (Lam _A _) = context _A
context (App _A _ _) = Extend _A
context (Sigma _A _B) = context _A

-- Extracts the type of a term.
termType :: Term -> Term
termType (Universe _Γ) = Universe _Γ
termType (Assume _A _) = _A
termType (Apply σ t) = Apply σ (termType t)
termType (Var _A) = Apply (SubstWeaken _A) _A
termType (Pi _A _B) = Universe (context _A)
termType (Lam _A b) = Pi _A (termType b)
termType (App _ _B _) = _B
termType (Sigma _A _B) = Universe (context _A)

{-
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
-}

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
    return (Pi _A' (Apply (SubstWeaken _A') _B'))
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