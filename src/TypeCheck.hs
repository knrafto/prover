module TypeCheck where

import           Control.Applicative
import           Control.Monad.Except
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

instance Show Context where
    showsPrec _ Empty = showString "∙"
    showsPrec _ _Γ = showParen True (go _Γ)
      where
        go Empty = showString "∙"
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

instance Show Subst where
    showsPrec _ (SubstWeaken _A) = showString "wk"
    showsPrec _ (SubstTerm t) = showString "⟨" . shows t . showString "⟩"
    showsPrec _ (SubstExtend σ _A) = shows σ . showString " ↑ " . shows _A

substDomain :: Subst -> Context
substDomain (SubstWeaken _A) = Extend _A
substDomain (SubstTerm t) = context t
substDomain (SubstExtend σ _A) = Extend (Apply σ _A)

substCodomain :: Subst -> Context
substCodomain (SubstWeaken _A) = context _A
substCodomain (SubstTerm t) = Extend (termType t)
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
    toSubscript _ = error "toSubscript: not a digit"

data Var
    -- If A : Tm Γ U, then v₀ : Var (Γ, A) A[wk].
    = VZ Term
    -- If B : Tm Γ U and v : Var Γ B, then vs(v) : Var (Γ, A) B[wk]
    | VS Term Var

instance Show Var where
    showsPrec _ v = showString "v" . showString (subscript (deBruijn v))

deBruijn :: Var -> Int
deBruijn (VZ _) = 0
deBruijn (VS _ v) = 1 + deBruijn v

fromDeBruijn :: Context -> Int -> Var
fromDeBruijn Empty _ = error "fromDeBruijn: empty context"
fromDeBruijn (Extend _A) 0 = VZ _A
fromDeBruijn (Extend _A) i = VS _A (fromDeBruijn (context _A) (i - 1))

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
    -- If A : Tm Γ U and B : Tm (Γ, A) U, then Σ(A, B) : Tm Γ U
    | Sigma Term Term

instance Show Term where
    showsPrec _ (Universe _) = showString "U"
    showsPrec _ (Assume n _ _) = showString (Text.unpack n)
    showsPrec _ (Metavar (VarId i) _ _) = showString "α" . showString (subscript i)
    showsPrec _ (Apply σ t) = shows t . showString "[" . shows σ . showString "]"
    showsPrec _ (Var v) = shows v
    showsPrec _ (Pi _A _B) = showString "Π(" . shows _A . showString ", " . shows _B . showString ")"
    showsPrec _ (Lam _ b) = showString "λ(" . shows b . showString ")"
    showsPrec _ (App _ _ f a) = showString "app(" . shows f . showString ", " . shows a . showString ")"
    showsPrec _ (Sigma _A _B) = showString "Σ(" . shows _A . showString ", " . shows _B . showString ")"

-- Extracts the context from a term.
context :: Term -> Context
context (Universe _Γ) = _Γ
context (Assume _ _Γ _) = _Γ
context (Metavar _ _Γ _) = _Γ
context (Apply σ _) = substDomain σ
context (Var v) = go v
  where
    go (VZ _A) = Extend _A
    go (VS _A _) = Extend _A
context (Pi _A _B) = context _A
context (Lam _A _) = context _A
context (App _A _ _ _) = context _A
context (Sigma _A _B) = context _A

-- Extracts the type of a term.
termType :: Term -> Term
termType (Universe _Γ) = Universe _Γ
termType (Assume _ _ _A) = _A
termType (Metavar _ _ _A) = _A
termType (Apply σ t) = Apply σ (termType t)
termType (Var v) = go v
  where
    go (VZ _A) = Apply (SubstWeaken _A) _A
    go (VS _A v') = Apply (SubstWeaken _A) (go v')
termType (Pi _A _B) = Universe (context _A)
termType (Lam _A b) = Pi _A (termType b)
termType (App _ _B _ a) = Apply (SubstTerm a) _B
termType (Sigma _A _B) = Universe (context _A)

data TcState = TcState
    -- Global definitions, and their values.
    { tcDefinitions :: Map Text Term
    -- Global assumptions, and their types.
    , tcAssumptions :: Map Text Term
    -- Next metavar id.
    , nextId :: !Int
    -- Metavar substitution.
    , subst :: Map VarId Term
    }

initialState :: TcState
initialState = TcState { tcDefinitions = Map.empty, tcAssumptions = Map.empty, nextId = 0, subst = Map.empty }

-- Note that StateT is layered over ExceptT, so that alternatives are explored
-- "in parallel" by duplicating state.
type TcM a = StateT TcState (ExceptT String IO) a

reportError :: TcM () -> TcM ()
reportError h = catchError h $ \e -> liftIO (putStrLn e)

freshVarId :: TcM VarId
freshVarId = do
    i <- gets nextId
    modify $ \s -> s { nextId = i + 1 }
    return (VarId i)

-- TODO: occurs check
assign :: VarId -> Term -> TcM ()
assign i t = modify $ \s -> s { subst = Map.insert i t (subst s) }

unificationFailure :: Term -> Term -> TcM a
unificationFailure t1 t2 = throwError $
    "Failed to unify in context: " ++ show (context t1) ++ "\n" ++
    "  " ++ show t1 ++ "\n" ++
    "  " ++ show t2 ++ "\n"

unify :: Term -> Term -> TcM ()
unify t1 t2 = do
    t1' <- reduce t1
    t2' <- reduce t2
    unify' t1' t2' <|> unify' t2' t1'

-- TODO: rewrite to be one-sided and try both sides in unify?
unify' :: Term -> Term -> TcM ()
unify' (Universe _) (Universe _) = return ()
unify' (Universe _) (Apply σ t) = unify (Universe (substCodomain σ)) t
unify' (Assume n1 _ _) (Assume n2 _ _) | n1 == n2 = return ()
unify' (Metavar i _ _) t = assign i t
unify' (Var (VZ _)) (Var (VZ _)) = return ()
unify' (Var (VS _ v1)) (Var (VS _ v2)) = unify (Var v1) (Var v2)
unify' (Apply (SubstWeaken _) t) (Var (VS _ v)) = unify t (Var v)
unify' (Apply (SubstTerm _) (Apply (SubstWeaken _) t1)) t2 = unify t1 t2
unify' (Pi _A1 _B1) (Pi _A2 _B2) = do
    unify _A1 _A2
    unify _B1 _B2
unify' (Pi _A _B) (Apply σ t) = do
    α <- freshVarId
    β <- freshVarId
    let _Γ = substCodomain σ
    let _A' = Metavar α _Γ (Universe _Γ)
    let _B' = Metavar β (Extend _A') (Universe (Extend _A'))
    unify t (Pi _A' _B')
    unify _A _A'
    unify _B _B'
unify' (Lam _ b1) (Lam _ b2) = unify b1 b2
unify' (App _ _ f1 a1) (App _ _ f2 a2) | isHeadNeutral f1 && isHeadNeutral f2 = do
    unify f1 f2
    unify a1 a2
-- Eta rule says that lam(app(f[wk], v₀))) = f for any f. Thus, if we have
-- app(f[wk], v₀)) = e, then we know f = lam(e).
unify' (App _A _ (Apply (SubstWeaken _) t1) (Var (VZ _))) t2 = unify t1 (Lam _A t2)
unify' (Sigma _A1 _B1) (Sigma _A2 _B2) = do
    unify _A1 _A2
    unify _B1 _B2
unify' (Sigma _A _B) (Apply σ t) = do
    α <- freshVarId
    β <- freshVarId
    let _Γ = substCodomain σ
    let _A' = Metavar α _Γ (Universe _Γ)
    let _B' = Metavar β (Extend _A') (Universe (Extend _A'))
    unify t (Sigma _A' _B')
    unify _A _A'
    unify _B _B'
unify' t1 t2 = unificationFailure t1 t2

-- Attempts to simplify a term. If there are no metavars, the result will be
-- a normal form.
-- TODO: reduce Pi and Sigma?
reduce :: Term -> TcM Term
reduce t@(Metavar i _ _) = do
    currentSubst <- gets subst
    -- TODO: path compression
    case Map.lookup i currentSubst of
        Nothing -> return t
        Just t' -> reduce t'
reduce (Apply σ t) = do
    t' <- reduce t
    case t' of
        Universe _ -> return $ Universe (substDomain σ)
        Assume name _ _A -> return $ Assume name (substDomain σ) (Apply σ _A)
        Var v -> reduce $ case (σ, v) of
            (SubstWeaken _A, _) -> Var (VS _A v)
            (SubstTerm a, VZ _) -> a
            (SubstTerm _, VS _ v') -> Var v'
            (SubstExtend σ' _, VZ _A) -> Var (VZ (Apply σ' _A))
            (SubstExtend σ' _A, VS _ v') ->
                Apply (SubstWeaken (Apply σ' _A)) (Apply σ' (Var v'))
        Pi _A _B -> reduce $ Pi (Apply σ _A) (Apply (SubstExtend σ _A) _B)
        Lam _A b -> reduce $ Lam (Apply σ _A) (Apply (SubstExtend σ _A) b)
        App _A _B f a -> reduce $ App (Apply σ _A) (Apply (SubstExtend σ _A) _B) (Apply σ f) (Apply σ a)
        Sigma _A _B -> reduce $ Sigma (Apply σ _A) (Apply (SubstExtend σ _A) _B)
        _ -> return $ Apply σ t'
reduce (Pi _A _B) = Pi <$> reduce _A <*> reduce _B
reduce (Lam _A b) = Lam _A <$> reduce b
reduce (App _A _B f a) = do
    f' <- reduce f
    a' <- reduce a
    case f' of
        Lam _ b -> reduce $ Apply (SubstTerm a') b
        _ -> return $ App _A _B f' a'
reduce (Sigma _A _B) = Sigma <$> reduce _A <*> reduce _B
reduce t = return t

-- Checks there are no redexes in an expression.
isHeadNeutral :: Term -> Bool
isHeadNeutral (Assume _ _ _) = True
isHeadNeutral (Var _) = True
isHeadNeutral (App _ _ f _) = isHeadNeutral f
isHeadNeutral _ = False

-- Searches for a term that has a given type.
prove :: Term -> TcM Term
prove _A = throwError $ "Could not prove " ++ show _A

typeCheck :: [Syntax.Statement] -> IO TcState
typeCheck statements = do
    result <- runExceptT (execStateT (mapM_ typeCheckStatement statements) initialState)
    case result of
        Left e -> fail e
        Right s -> return s

-- TODO: also substitute for metavars before printing.
typeCheckStatement :: Syntax.Statement -> TcM ()
typeCheckStatement (Syntax.Define name body) = do
    bodyTerm <- typeCheckExpr Empty [] body
    bodyTerm' <- reduce bodyTerm
    modify $ \s -> s { tcDefinitions = Map.insert name bodyTerm' (tcDefinitions s) }
typeCheckStatement (Syntax.Assume name ty) = do
    tyTerm <- typeCheckExpr Empty [] ty
    tyTerm' <- reduce tyTerm
    modify $ \s -> s { tcAssumptions = Map.insert name tyTerm' (tcAssumptions s) }
typeCheckStatement (Syntax.Prove ty) = do
    tyTerm <- typeCheckExpr Empty [] ty
    tyTerm' <- reduce tyTerm
    reportError . void $ prove tyTerm'

weakenGlobal :: Context -> Term -> Term
weakenGlobal Empty t = t
weakenGlobal (Extend _A) t = Apply (SubstWeaken _A) (weakenGlobal (context _A) t) 

typeCheckExpr :: Context -> [Text] -> Syntax.Expr -> TcM Term
typeCheckExpr _Γ _ Syntax.Hole = do
    -- We generate variables for both the hole itself, and its type. Luckily
    -- for now we don't have to do this forever, since the type of any type is
    -- the universe.
    termVarId <- freshVarId
    typeVarId <- freshVarId
    return (Metavar termVarId _Γ (Metavar typeVarId _Γ (Universe _Γ)))
typeCheckExpr _Γ names (Syntax.Var name) = do
    definitions <- gets tcDefinitions
    assumptions <- gets tcAssumptions
    case () of
        _ | Just i <- elemIndex name names -> return (Var (fromDeBruijn _Γ i))
          | Just body <- Map.lookup name definitions ->
                return (weakenGlobal _Γ body)
          | Just _A <- Map.lookup name assumptions ->
                return (Assume name _Γ _A)
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
checkIsType t = reportError $ unify (termType t) (Universe (context t))

typeCheckApp :: Term -> [Term] -> TcM Term
typeCheckApp f [] = return f
typeCheckApp f (arg : args) = do
    varId <- freshVarId
    let _Γ = context f
    let _A = termType arg
    let _B = Metavar varId _Γ (Universe _Γ)
    reportError $ unify (termType f) (Pi _A _B)
    typeCheckApp (App _A _B f arg) args