module TypeCheck where

import           Control.Monad.State
import           Data.List
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict as Map
import           Data.Text                      ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Lazy as L
import           Text.Pretty.Simple

import qualified Syntax

-- This description of type theory is based on §A.2 in the HoTT book.

-- A context is roughly a list of variables. It represents a "tower" of
-- dependent types. We leave variables unnamed, and use De Bruijn indexes.
-- In this representation, the "outermost" type has index 0.
newtype Context = Context [Term]
    deriving (Show)

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
data Term
    -- Γ ⊢ x_i : A_i
    = Var Context !Int
    -- Γ ⊢ Type : Type
    | Universe Context
    -- If Γ ⊢ A : Type, then by assumption Γ ⊢ a : A
    | Assume Context Text Term
    -- If Γ ⊢ A : Type and Γ, x : A ⊢ B : Type then Γ ⊢ Π (x : A). B : Type
    | Pi Term Term
    -- If Γ ⊢ A : Type and Γ, x : A ⊢ b : B then Γ ⊢ λ (x : A). b : Π (x : A). B
    | Lam Term Term
    -- If Γ ⊢ f : Π (x : A). B and Γ ⊢ a : A then Γ ⊢ f(a) : B[a/x]
    | App Term Term 
    -- If Γ ⊢ A : Type and Γ, x : A ⊢ B : Type then Γ ⊢ Π (x : A). B : Type
    | Sigma Term Term
    deriving (Show)

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
subst ctx e (Var _ i)
    | i < k = Var ctx i
    | i == k = weaken ctx 0 e
    | otherwise = Var ctx (i - 1)
  where
    k = contextLength ctx - contextLength (domain e)
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
termType t@(App f x) = case normalize (termType f) of
    Pi a b -> subst (domain x) x b
    _ -> error $ "termType: type of function is not a Π-type" ++ show t
termType t@(Sigma a b) = Universe (domain t)

-- Decides syntactic equality.
syntacticallyEqual :: Term -> Term -> Bool
syntacticallyEqual (Var _ i) (Var _ j) = i == j
syntacticallyEqual (Universe _) (Universe _) = True
syntacticallyEqual (Assume _ n _) (Assume _ m _) = n == m
syntacticallyEqual (Pi a b) (Pi c d) = syntacticallyEqual a c && syntacticallyEqual b d
syntacticallyEqual (Lam a b) (Lam c d) = syntacticallyEqual a c && syntacticallyEqual b d
syntacticallyEqual (App f x) (Pi g y) = syntacticallyEqual f g && syntacticallyEqual x y
syntacticallyEqual (Sigma a b) (Sigma c d) = syntacticallyEqual a c && syntacticallyEqual b d
syntacticallyEqual _ _ = False

-- Reduces each term to a normal form. The only judgemental equality is β-reduction.
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
judgmentallyEqual :: Term -> Term -> Bool
judgmentallyEqual t1 t2 = syntacticallyEqual (normalize t1) (normalize t2)

data TcState = TcState
    -- Global definitions, and their values.
    { tcDefinitions :: Map Text Term
    -- Global assumptions, and their types.
    , tcAssumptions :: Map Text Term
    } deriving (Show)

initialState :: TcState
initialState = TcState { tcDefinitions = Map.empty, tcAssumptions = Map.empty }

type TcM a = StateT TcState IO a

checkIsType :: Term -> TcM ()
checkIsType t = case normalize (termType t) of
    Universe _ -> return ()
    _ -> fail "not a type"

typeCheckApp :: Term -> [Term] -> TcM Term
typeCheckApp f [] = return f
typeCheckApp f (arg : args) = do
    (a, b) <- case normalize (termType f) of
        Pi a b -> return (a, b)
        _ -> fail $ "not a Π-type"
    unless (judgmentallyEqual a (termType arg)) $
        fail $ "argument type of:\n" ++ L.unpack (pShow f)
            ++ "\nnamely:\n" ++ L.unpack (pShow a)
            ++ "\ndoes not match type of:\n" ++ L.unpack (pShow arg)
            ++ "\nnamely:\n" ++ L.unpack (pShow (normalize (termType arg)))
    typeCheckApp (App f arg) args

typeCheckExpr :: Context -> [Text] -> Syntax.Expr -> TcM Term
typeCheckExpr ctx names (Syntax.Var name) = do
    definitions <- gets tcDefinitions
    assumptions <- gets tcAssumptions
    case () of
        _ | Just i <- elemIndex name names ->
                return (Var ctx i)
          | Just body <- Map.lookup name definitions ->
                return (weaken ctx 0 body)
          | Just ty <- Map.lookup name assumptions ->
                return (Assume ctx name (weaken ctx 0 ty))
          | otherwise ->
                fail $ "unbound name " ++ Text.unpack name
typeCheckExpr ctx names Syntax.Universe = return (Universe ctx)
typeCheckExpr ctx names (Syntax.Pi name a b) = do
    a' <- typeCheckExpr ctx names a
    checkIsType a'
    b' <- typeCheckExpr (extend ctx a') (name : names) b
    checkIsType b'
    return (Pi a' b')
typeCheckExpr ctx names (Syntax.Arrow a b) = do
    a' <- typeCheckExpr ctx names a
    checkIsType a'
    b' <- typeCheckExpr ctx names b
    checkIsType b'
    return (Pi a' (weaken (extend ctx a') 0 b'))
typeCheckExpr ctx names (Syntax.Lam name a b) = do
    a' <- typeCheckExpr ctx names a
    checkIsType a'
    b' <- typeCheckExpr (extend ctx a') (name : names) b
    return (Lam a' b')
typeCheckExpr ctx names (Syntax.App f args) = do
    f' <- typeCheckExpr ctx names f
    args' <- mapM (typeCheckExpr ctx names) args
    typeCheckApp f' args'
typeCheckExpr ctx names (Syntax.Sigma name a b) = do
    a' <- typeCheckExpr ctx names a
    checkIsType a'
    b' <- typeCheckExpr (extend ctx a') (name : names) b
    checkIsType b'
    return (Sigma a' b')

typeCheckStatement :: Syntax.Statement -> TcM ()
typeCheckStatement (Syntax.Define name body) = do
    body' <- typeCheckExpr emptyContext [] body
    modify $ \s -> s { tcDefinitions = Map.insert name body' (tcDefinitions s) }
typeCheckStatement (Syntax.Assume name ty) = do
    ty' <- typeCheckExpr emptyContext [] ty
    modify $ \s -> s { tcAssumptions = Map.insert name ty' (tcAssumptions s) }
typeCheckStatement (Syntax.Prove _) = fail ":prove not implemented"

typeCheck :: [Syntax.Statement] -> IO TcState
typeCheck statements = execStateT (mapM_ typeCheckStatement statements) initialState