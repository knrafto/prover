{-# LANGUAGE TemplateHaskell #-}
module TypeCheck where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Foldable
import           Data.List
import           Data.Maybe
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict as Map
import           Data.Text                      ( Text )
import qualified Data.Text as Text
import           Data.Tree
import           HFlags

import           Search
import qualified Syntax

defineFlag "print_trace" False "Print trace of program execution."

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

instance Eq Subst where
    (SubstWeaken _) == (SubstWeaken _) = True
    (SubstTerm t1) == (SubstTerm t2) = t1 == t2
    (SubstExtend σ1 _) == (SubstExtend σ2 _) = σ1 == σ2
    _ == _ = False

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

instance Eq Var where
    (VZ _) == (VZ _) = True
    (VS _ v1) == (VS _ v2) = v1 == v2
    _ == _ = False

instance Show Var where
    showsPrec _ v = showString "v" . showString (subscript (deBruijn v))

deBruijn :: Var -> Int
deBruijn (VZ _) = 0
deBruijn (VS _ v) = 1 + deBruijn v

fromDeBruijn :: Context -> Int -> Var
fromDeBruijn Empty _ = error "fromDeBruijn: empty context"
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
    (Universe _) == (Universe _) = True
    (Assume n1 _ _) == (Assume n2 _ _) = n1 == n2
    (Metavar i1 _ _) == (Metavar i2 _ _) = i1 == i2
    (Apply σ1 t1) == (Apply σ2 t2) = σ1 == σ2 && t1 == t2
    (Var v1) == (Var v2) = v1 == v2
    (Pi _A1 _B1) == (Pi _A2 _B2) = _A1 == _A2 && _B1 == _B2
    (Lam _ b1) == (Lam _ b2) = b1 == b2
    (App _ _ f1 a1) == (App _ _ f2 a2) = f1 == f2 && a1 == a2
    _ == _ = False

instance Show Term where
    showsPrec _ (Universe _) = showString "U"
    showsPrec _ (Assume n _ _) = showString (Text.unpack n)
    showsPrec _ (Metavar (VarId i) _ _) = showString "α" . showString (subscript i)
    showsPrec _ (Apply σ t) = shows t . showString "[" . shows σ . showString "]"
    showsPrec _ (Var v) = shows v
    showsPrec _ (Pi _A _B) = showString "Π(" . shows _A . showString ", " . shows _B . showString ")"
    showsPrec _ (Lam _ b) = showString "λ(" . shows b . showString ")"
    showsPrec _ (App _ _ f a) = showString "app(" . shows f . showString ", " . shows a . showString ")"

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
context (Pi _A _) = context _A
context (Lam _A _) = context _A
context (App _A _ _ _) = context _A

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

weakenGlobal :: Context -> Term -> Term
weakenGlobal Empty t = t
weakenGlobal (Extend _A) t = Apply (SubstWeaken _A) (weakenGlobal (context _A) t)

data TcState = TcState
    -- Global definitions, and their values.
    { envDefinitions :: Map Text Term
    -- Global assumptions, and their types.
    , envAssumptions :: Map Text Term
    -- Next metavar id.
    , nextId :: !Int
    -- Metavar substitution.
    , subst :: Map VarId Term
    -- Unsolved unification equations.
    , unsolvedEquations :: [(Term, Term)]
    }

initialState :: TcState
initialState = TcState
    { envDefinitions = Map.empty
    , envAssumptions = Map.empty
    , nextId = 0
    , subst = Map.empty
    , unsolvedEquations = []
    }

type TcM a = SearchM TcState a

-- Runs a search, reporting any failure
runTcM :: TcState -> TcM a -> IO (Maybe (a, TcState))
runTcM s m = do
    let Result as bs = runSearch m s
    when flags_print_trace $ putStr (drawForest bs)
    return (listToMaybe as)

-- Generate a metavar for the given context and type.
freshMetavar :: Context -> Term -> TcM Term
freshMetavar _Γ _A = do
    i <- gets nextId
    modify $ \s -> s { nextId = i + 1 }
    return $ Metavar (VarId i) _Γ _A

saveEquation :: Term -> Term -> TcM ()
saveEquation t1 t2 = modify $ \s -> s { unsolvedEquations = (t1, t2) : unsolvedEquations s }

-- TODO: occurs check
assign :: VarId -> Term -> TcM ()
assign i t = do
    eqs <- gets unsolvedEquations
    modify $ \s -> s { subst = Map.insert i t (subst s), unsolvedEquations = [] }
    unless (null eqs) $
        trace "Retrying unsolved equations" $
            forM_ eqs $ \(t1, t2) -> unify t1 t2

unificationFailure :: Term -> Term -> TcM a
unificationFailure t1 t2 = throw $
    "Failed to unify in context: " ++ show (context t1) ++ "\n" ++
    "  " ++ show t1 ++ "\n" ++
    "  " ++ show t2

checkSolved :: TcM ()
checkSolved = do
    eqs <- gets unsolvedEquations
    modify $ \s -> s { unsolvedEquations = [] }
    case eqs of
        [] -> return ()
        ((t1, t2):_) -> unificationFailure t1 t2

unify :: Term -> Term -> TcM ()
unify t1 t2 = do
    t1' <- reduce t1
    t2' <- reduce t2
    trace ("Unifying in context: " ++ show (context t1) ++ "\n  " ++ show t1' ++ "\n  " ++ show t2') $
        unify' t1' t2'

unify' :: Term -> Term -> TcM ()
unify' t1 t2 | t1 == t2 = return ()
unify' (Universe _) (Universe _) = return ()
unify' (Universe _) (Apply σ t) = unify (Universe (substCodomain σ)) t
unify' (Apply σ t) (Universe _) = unify (Universe (substCodomain σ)) t
unify' (Assume n1 _ _) (Assume n2 _ _) | n1 == n2 = return ()
unify' (Metavar i _ _) t = assign i t
unify' t (Metavar i _ _) = assign i t
unify' (Var (VZ _)) (Var (VZ _)) = return ()
unify' (Var (VS _ v1)) (Var (VS _ v2)) = unify (Var v1) (Var v2)
unify' (Apply (SubstWeaken _) t) (Var (VS _ v)) = unify t (Var v)
unify' (Var (VS _ v)) (Apply (SubstWeaken _) t) = unify t (Var v)
unify' (Pi _A1 _B1) (Pi _A2 _B2) = do
    unify _A1 _A2
    unify _B1 _B2
unify' (Pi _A _B) (Apply σ t) = do
    let _Γ = substCodomain σ
    _A' <- freshMetavar _Γ (Universe _Γ)
    _B' <- freshMetavar (Extend _A') (Universe (Extend _A'))
    unify t (Pi _A' _B')
    unify _A (Apply σ _A')
    unify _B (Apply (SubstExtend σ _A') _B')
unify' t1@(Apply _ _) t2@(Pi _ _) = unify t2 t1
unify' (Lam _ b1) (Lam _ b2) = unify b1 b2
unify' (App _ _ f1 a1) (App _ _ f2 a2) | isWeakNormal f1 && isWeakNormal f2 = do
    unify f1 f2
    unify a1 a2
-- Eta rule says that lam(app(f[wk], v₀))) = f for any f. Thus, if we have
-- app(f[wk], v₀)) = e, then we know f = lam(e).
unify' (App _A _ (Apply (SubstWeaken _) t1) (Var (VZ _))) t2 = unify t1 (Lam _A t2)
unify' t2 (App _A _ (Apply (SubstWeaken _) t1) (Var (VZ _))) = unify t1 (Lam _A t2)
-- Two-level eta rule.
-- TODO: infer this from principles instead of hacking it in.
unify' (App _A _ (App _B _ (Apply (SubstWeaken _) (Apply (SubstWeaken _) t1)) (Var (VS _ (VZ _)))) (Var (VZ _))) t2 = unify t1 (Lam _A (Lam _B t2))
unify' t2 (App _A _ (App _B _ (Apply (SubstWeaken _) (Apply (SubstWeaken _) t1)) (Var (VS _ (VZ _)))) (Var (VZ _))) = unify t1 (Lam _A (Lam _B t2))
-- If two head-neutral terms don't unify, the terms are unequal; otherwise,
-- save it for later.
unify' t1 t2
    | isWeakNormal t1 && isWeakNormal t2 = unificationFailure t1 t2
    | otherwise = saveEquation t1 t2

-- Attempts to simplify a term. If there are no metavars, the result will be
-- a normal form.
-- TODO: reduce contexts, types too?
reduce :: Term -> TcM Term
reduce t@(Universe _) = return t
reduce t@(Assume _ _ _) = return t
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
        Metavar _ _ _ -> return $ Apply σ t'
        Apply τ t'' -> case (σ, τ) of
            (SubstTerm _, SubstWeaken _) -> return t''
            (SubstExtend σ' _, SubstWeaken _A) -> reduce $ Apply (SubstWeaken (Apply σ' _A)) (Apply σ' t'')
            _ -> return $ Apply σ t'
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
reduce t@(Var _) = return t
reduce (Pi _A _B) = Pi <$> reduce _A <*> reduce _B
reduce (Lam _A b) = Lam _A <$> reduce b
reduce (App _A _B f a) = do
    f' <- reduce f
    a' <- reduce a
    case f' of
        Lam _ b -> reduce $ Apply (SubstTerm a') b
        _ -> return $ App _A _B f' a'

-- Checks there are no redexes in the App "spine" of a term.
-- TODO: put this on firm foundation.
isWeakNormal :: Term -> Bool
isWeakNormal (Lam _ _) = True
isWeakNormal t = isWeakNeutral t
  where
    isWeakNeutral (Universe _) = True
    isWeakNeutral (Assume _ _ _) = True
    isWeakNeutral (Metavar _ _ _) = False
    isWeakNeutral (Apply _ _) = False
    isWeakNeutral (Var _) = True
    isWeakNeutral (Pi _ _) = True
    isWeakNeutral (Lam _ _) = False
    isWeakNeutral (App _ _ f _) = isWeakNeutral f

-- Tries to unify something with the given term (which is most likely a metavar).
search :: Term -> TcM ()
search t = do
    t' <- reduce t
    case t' of
        Metavar _ _ _ ->
            trace ("Searching " ++ show t' ++ " : " ++ show (termType t')) $
                searchAssumptions t' <|> searchLam t'
        -- Assume term is solved.
        -- TODO: check more carefully.
        _ -> return ()

-- Try to unify an unknown term with a guess.
accept :: Term -> Term -> TcM ()
accept t guess = do
    guessType <- reduce (termType guess)
    -- Prune branches where the guess is too general (e.g. metavar applied to args).
    guard (isWeakNormal guessType)
    _A <- reduce (termType t)
    trace ("Trying " ++ show guess ++ " for " ++ show _A) $ do
        unify (termType t) (termType guess)
        unify t guess

searchAssumptions :: Term -> TcM ()
searchAssumptions t = do
    assumptions <- gets envAssumptions
    asum $ map (\(name, ty) -> try (weakenGlobal _Γ (Assume name Empty ty))) (Map.toList assumptions)
  where
    _Γ = context t

    try p = accept t p <|> tryApp p

    tryApp p = do
        ty <- reduce (termType p)
        case ty of
            Pi _A _B -> do
                α <- freshMetavar _Γ _A
                try (App _A _B p α)
                search α
            _ -> empty

searchLam :: Term -> TcM ()
searchLam t = do
    let _Γ = context t
    _A <- freshMetavar _Γ (Universe _Γ)
    let _Γ' = Extend _A
    _B <- freshMetavar _Γ' (Universe _Γ')
    β <- freshMetavar _Γ' _B
    accept t (Lam _A β)
    search β

typeCheck :: [Syntax.LStatement] -> IO TcState
typeCheck = go initialState
  where
    go s [] = return s
    go s (stmt:rest) = do
        s' <- typeCheckStatement s stmt
        go s' rest

typeCheckStatement :: TcState -> Syntax.LStatement -> IO TcState
typeCheckStatement s stmt = case Syntax.unLoc stmt of
    Syntax.Define name params ty body -> do
        putStrLn $ "Checking " ++ Text.unpack name
        result <- runTcM s $ do
            bodyTerm <- typeCheckLam Empty [] params body
            case ty of
                Nothing -> return ()
                Just ty' -> do
                    tyTerm <- typeCheckPi Empty [] params ty'
                    unify (termType bodyTerm) tyTerm
            checkSolved
            reduce bodyTerm
        case result of
            Nothing -> do
                putStrLn $ "Error in " ++ Text.unpack name
                return s
            Just (bodyTerm, s') -> do
                putStrLn $ Text.unpack name ++ " := " ++ show bodyTerm
                return $ s' { envDefinitions = Map.insert name bodyTerm (envDefinitions s') }
    Syntax.Assume name ty -> do
        putStrLn $ "Checking " ++ Text.unpack name
        result <- runTcM s $ do
            tyTerm <- typeCheckExpr Empty [] ty
            checkSolved
            reduce tyTerm
        case result of
            Nothing -> do
                putStrLn $ "Error in " ++ Text.unpack name
                return s
            Just (tyTerm, s') -> do
                putStrLn $ ":assume " ++ Text.unpack name ++ " : " ++ show tyTerm
                return $ s' { envAssumptions = Map.insert name tyTerm (envAssumptions s') }
    Syntax.Prove name ty -> do
        putStrLn $ "Checking " ++ Text.unpack name
        result <- runTcM s $ do
            tyTerm <- typeCheckExpr Empty [] ty
            tyTerm' <- reduce tyTerm
            α <- freshMetavar (context tyTerm') tyTerm'
            search α
            checkSolved
            reduce α
        case result of
            Nothing -> do
                putStrLn $ "Error in " ++ Text.unpack name
                return s
            Just (bodyTerm, s') -> do
                putStrLn $ Text.unpack name ++ " := " ++ show bodyTerm
                return $ s' { envDefinitions = Map.insert name bodyTerm (envDefinitions s') }

typeCheckExpr :: Context -> [Text] -> Syntax.LExpr -> TcM Term
typeCheckExpr _Γ names expr = case Syntax.unLoc expr of
    Syntax.Hole -> typeCheckHole _Γ
    Syntax.Var name -> do
        definitions <- gets envDefinitions
        assumptions <- gets envAssumptions
        case () of
            _   | Just i <- elemIndex name names -> return (Var (fromDeBruijn _Γ i))
                | Just body <- Map.lookup name definitions ->
                        return (weakenGlobal _Γ body)
                | Just _A <- Map.lookup name assumptions ->
                        return (weakenGlobal _Γ (Assume name Empty _A))
                | otherwise ->
                        fail $ "unbound name: " ++ Text.unpack name
    Syntax.Universe -> return (Universe _Γ)
    Syntax.Equal a b -> do
        f' <- typeCheckBuiltIn _Γ "Id"
        _A <- typeCheckHole _Γ
        a' <- typeCheckExpr _Γ names a
        b' <- typeCheckExpr _Γ names b
        typeCheckApp f' [_A, a', b']
    Syntax.Pi params _B -> typeCheckPi _Γ names params _B
    Syntax.Arrow _A _B -> do
        _A' <- typeCheckExpr _Γ names _A
        checkIsType _A'
        _B' <- typeCheckExpr _Γ names _B
        checkIsType _B'
        return (Pi _A' (Apply (SubstWeaken _A') _B'))
    Syntax.Lam params b -> typeCheckLam _Γ names params b
    Syntax.App f args -> do
        f' <- typeCheckExpr _Γ names f
        args' <- mapM (typeCheckExpr _Γ names) args
        typeCheckApp f' args'
    Syntax.Sigma params _B -> typeCheckSigma _Γ names params _B
    Syntax.Times _A _B -> do
        _A' <- typeCheckExpr _Γ names _A
        _B' <- typeCheckExpr _Γ names _B
        f <- typeCheckBuiltIn _Γ "Σ'"
        typeCheckApp f [_A', Lam _A' (Apply (SubstWeaken _A') _B')]
    Syntax.Tuple args -> do
        args' <- mapM (typeCheckExpr _Γ names) args
        typeCheckTuple args'

typeCheckPi :: Context -> [Text] -> [Syntax.Param] -> Syntax.LExpr -> TcM Term
typeCheckPi _Γ names [] _B = typeCheckExpr _Γ names _B
typeCheckPi _Γ names ((name, _A):params) _B = do
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    _B' <- typeCheckPi (Extend _A') (name : names) params _B
    checkIsType _B'
    return (Pi _A' _B')

typeCheckLam :: Context -> [Text] -> [Syntax.Param] -> Syntax.LExpr -> TcM Term
typeCheckLam _Γ names [] b = typeCheckExpr _Γ names b
typeCheckLam _Γ names ((name, _A):params) b = do
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    b' <- typeCheckLam (Extend _A') (name : names) params b
    return (Lam _A' b')

typeCheckSigma :: Context -> [Text] -> [Syntax.Param] -> Syntax.LExpr -> TcM Term
typeCheckSigma _Γ names [] _B = typeCheckExpr _Γ names _B
typeCheckSigma _Γ names ((name, _A):params) _B = do
    _A' <- typeCheckExpr _Γ names _A
    _B' <- typeCheckSigma (Extend _A') (name : names) params _B
    f <- typeCheckBuiltIn _Γ "Σ'"
    typeCheckApp f [_A', Lam _A' _B']

typeCheckBuiltIn :: Context -> String -> TcM Term
typeCheckBuiltIn _Γ name = do
    let name' = Text.pack name
    assumptions <- gets envAssumptions
    case Map.lookup name' assumptions of
        Just _A -> return (weakenGlobal _Γ (Assume name' Empty _A))
        _ -> fail $ "can't find built-in: " ++ name

typeCheckHole :: Context -> TcM Term
typeCheckHole _Γ = do
    -- We generate variables for both the hole itself, and its type. Luckily
    -- for now we don't have to do this forever, since the type of any type is
    -- the universe.
    _A <- freshMetavar _Γ (Universe _Γ)
    freshMetavar _Γ _A

checkIsType :: Term -> TcM ()
checkIsType t = unify (termType t) (Universe (context t))

typeCheckApp :: Term -> [Term] -> TcM Term
typeCheckApp f [] = return f
typeCheckApp f (arg : args) = do
    let _Γ = context f
    let _A = termType arg
    _B <- freshMetavar _Γ (Universe _Γ)
    unify (termType f) (Pi _A _B)
    typeCheckApp (App _A _B f arg) args

typeCheckTuple :: [Term] -> TcM Term
typeCheckTuple [] = error "typeCheckTuple: empty tuple"
typeCheckTuple [t] = return t
typeCheckTuple (a:ts) = do
    let _Γ = context a
    let _A = termType a
    let _Γ' = Extend _A
    _B <- freshMetavar _Γ' (Universe _Γ')
    b <- typeCheckTuple ts
    pair <- typeCheckBuiltIn _Γ "pair"
    typeCheckApp pair [_A, _B, a, b]
