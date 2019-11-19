{-# LANGUAGE LambdaCase #-}
module TypeCheck where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Foldable
import           Data.List
import           Data.Maybe
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Tree

import qualified Flags
import           Location
import           Naming
import           Search
import           Syntax                         ( Expr
                                                , Param
                                                , Statement
                                                )
import qualified Syntax
import           Term

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
initialState = TcState { envDefinitions    = Map.empty
                       , envAssumptions    = Map.empty
                       , nextId            = 0
                       , subst             = Map.empty
                       , unsolvedEquations = []
                       }

type TcM a = SearchM TcState a

-- Runs a search, reporting any failure
runTcM :: TcState -> TcM a -> IO (Maybe (a, TcState))
runTcM s m = do
    let Result as bs = runSearch m s
    when Flags.print_trace $ putStr (drawForest bs)
    return (listToMaybe as)

-- Generate a metavar for the given context and type.
freshMetavar :: Context -> Term -> TcM Term
freshMetavar _Γ _A = do
    i <- gets nextId
    modify $ \s -> s { nextId = i + 1 }
    return $ Metavar (VarId i) _Γ _A

saveEquation :: Term -> Term -> TcM ()
saveEquation t1 t2 =
    modify $ \s -> s { unsolvedEquations = (t1, t2) : unsolvedEquations s }

-- TODO: occurs check
assign :: VarId -> Term -> TcM ()
assign i t = do
    eqs <- gets unsolvedEquations
    modify $ \s ->
        s { subst = Map.insert i t (subst s), unsolvedEquations = [] }
    unless (null eqs) $ trace "Retrying unsolved equations" $ forM_
        eqs
        (uncurry unify)

unificationFailure :: Term -> Term -> TcM a
unificationFailure t1 t2 =
    throw
        $  "Failed to unify in context: "
        ++ show (context t1)
        ++ "\n"
        ++ "  "
        ++ show t1
        ++ "\n"
        ++ "  "
        ++ show t2

checkSolved :: TcM ()
checkSolved = do
    eqs <- gets unsolvedEquations
    modify $ \s -> s { unsolvedEquations = [] }
    case eqs of
        []             -> return ()
        ((t1, t2) : _) -> unificationFailure t1 t2

unify :: Term -> Term -> TcM ()
unify t1 t2 = do
    t1' <- reduce t1
    t2' <- reduce t2
    trace
            (  "Unifying in context: "
            ++ show (context t1)
            ++ "\n  "
            ++ show t1'
            ++ "\n  "
            ++ show t2'
            )
        $ unify' t1' t2'

unify' :: Term -> Term -> TcM ()
unify' t1 t2 | t1 == t2                           = return ()
unify' (Universe _) (Universe _)                  = return ()
unify' (Universe _) (Apply σ t) = unify (Universe (substCodomain σ)) t
unify' (Apply σ t) (Universe _) = unify (Universe (substCodomain σ)) t
unify' (Assume n1 _ _) (Assume n2 _ _) | n1 == n2 = return ()
unify' (Metavar i _ _)           t                           = assign i t
unify' t                         (Metavar i _ _            ) = assign i t
unify' (Var (VZ _   )          ) (Var (VZ _   )            ) = return ()
unify' (Var (VS _ v1)) (Var (VS _ v2)) = unify (Var v1) (Var v2)
unify' (Apply (SubstWeaken _) t) (Var (VS _ v )            ) = unify t (Var v)
unify' (Var (VS _ v)           ) (Apply (SubstWeaken _) t  ) = unify t (Var v)
unify' (Pi _A1 _B1             ) (Pi    _A2             _B2) = do
    unify _A1 _A2
    unify _B1 _B2
unify' (Pi _A _B) (Apply σ t) = do
    let _Γ = substCodomain σ
    _A' <- freshMetavar _Γ (Universe _Γ)
    _B' <- freshMetavar (Extend _A') (Universe (Extend _A'))
    unify t  (Pi _A' _B')
    unify _A (Apply σ _A')
    unify _B (Apply (SubstExtend σ _A') _B')
unify' t1@(Apply _ _ ) t2@(Pi  _ _ ) = unify t2 t1
unify' (   Lam   _ b1) (   Lam _ b2) = unify b1 b2
unify' (App _ _ f1 a1) (App _ _ f2 a2) | isWeakNormal f1 && isWeakNormal f2 = do
    unify f1 f2
    unify a1 a2
-- Eta rule says that lam(app(f[wk], v₀))) = f for any f. Thus, if we have
-- app(f[wk], v₀)) = e, then we know f = lam(e).
unify' (App _A _ (Apply (SubstWeaken _) t1) (Var (VZ _))) t2 =
    unify t1 (Lam _A t2)
unify' t2 (App _A _ (Apply (SubstWeaken _) t1) (Var (VZ _))) =
    unify t1 (Lam _A t2)
-- Two-level eta rule.
-- TODO: infer this from principles instead of hacking it in.
unify' (App _A _ (App _B _ (Apply (SubstWeaken _) (Apply (SubstWeaken _) t1)) (Var (VS _ (VZ _)))) (Var (VZ _))) t2
    = unify t1 (Lam _A (Lam _B t2))
unify' t2 (App _A _ (App _B _ (Apply (SubstWeaken _) (Apply (SubstWeaken _) t1)) (Var (VS _ (VZ _)))) (Var (VZ _)))
    = unify t1 (Lam _A (Lam _B t2))
-- Eta for var.
unify' t1@(Lam _A b) t2@(Var _   ) = unify' t1 (etaExpand _A (termType b) t2)
unify' t1@(Var _   ) t2@(Lam _A b) = unify' (etaExpand _A (termType b) t1) t2
-- If two head-neutral terms don't unify, the terms are unequal; otherwise,
-- save it for later.
unify' t1 t2 | isWeakNormal t1 && isWeakNormal t2 = unificationFailure t1 t2
             | otherwise                          = saveEquation t1 t2

-- Attempts to simplify a term. If there are no metavars, the result will be
-- a normal form.
-- TODO: reduce contexts, types too?
reduce :: Term -> TcM Term
reduce t@(Universe _   ) = return t
reduce t@(Assume  _ _ _) = return t
reduce t@(Metavar i _ _) = do
    currentSubst <- gets subst
    -- TODO: path compression
    case Map.lookup i currentSubst of
        Nothing -> return t
        Just t' -> reduce t'
reduce (Apply σ t) = do
    t' <- reduce t
    case t' of
        Universe _        -> return $ Universe (substDomain σ)
        Assume  name _ _A -> return $ Assume name (substDomain σ) (Apply σ _A)
        Metavar _    _ _  -> return $ Apply σ t'
        Apply τ t''       -> case (σ, τ) of
            (SubstTerm _, SubstWeaken _) -> return t''
            (SubstExtend σ' _, SubstWeaken _A) ->
                reduce $ Apply (SubstWeaken (Apply σ' _A)) (Apply σ' t'')
            _ -> return $ Apply σ t'
        Var v -> reduce $ case (σ, v) of
            (SubstWeaken _A  , _      ) -> Var (VS _A v)
            (SubstTerm   a   , VZ _   ) -> a
            (SubstTerm   _   , VS _ v') -> Var v'
            (SubstExtend σ' _, VZ _A  ) -> Var (VZ (Apply σ' _A))
            (SubstExtend σ' _A, VS _ v') ->
                Apply (SubstWeaken (Apply σ' _A)) (Apply σ' (Var v'))
        Pi  _A _B     -> reduce $ Pi (Apply σ _A) (Apply (SubstExtend σ _A) _B)
        Lam _A b      -> reduce $ Lam (Apply σ _A) (Apply (SubstExtend σ _A) b)
        App _A _B f a -> reduce $ App (Apply σ _A)
                                      (Apply (SubstExtend σ _A) _B)
                                      (Apply σ f)
                                      (Apply σ a)
reduce t@(Var _        ) = return t
reduce (  Pi  _A _B    ) = Pi <$> reduce _A <*> reduce _B
reduce (  Lam _A b     ) = Lam _A <$> reduce b
reduce (  App _A _B f a) = do
    f' <- reduce f
    a' <- reduce a
    case f' of
        Lam _ b -> reduce $ Apply (SubstTerm a') b
        _       -> return $ App _A _B f' a'

-- Tries to unify something with the given term (which is most likely a metavar).
search :: Term -> TcM ()
search t = do
    t' <- reduce t
    case t' of
        Metavar _ _ _ ->
            trace ("Searching " ++ show t' ++ " : " ++ show (termType t'))
                $   searchAssumptions t'
                <|> searchLam t'
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
        unify t            guess

searchAssumptions :: Term -> TcM ()
searchAssumptions t = do
    assumptions <- gets envAssumptions
    asum $ map (\(name, ty) -> try (weakenGlobal _Γ (Assume name Empty ty)))
               (Map.toList assumptions)
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
    β  <- freshMetavar _Γ' _B
    accept t (Lam _A β)
    search β

typeCheck :: [Statement N] -> IO TcState
typeCheck = go initialState
  where
    go s []            = return s
    go s (stmt : rest) = do
        s' <- typeCheckStatement s stmt
        go s' rest

typeCheckStatement :: TcState -> Statement N -> IO TcState
typeCheckStatement s = \case
    Syntax.Define ident params ty body -> do
        let name = unLoc (usage ident)
        putStrLn $ "Checking " ++ Text.unpack name
        result <- runTcM s $ do
            bodyTerm <- typeCheckLam Empty [] params body
            case ty of
                Nothing  -> return ()
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
                putStrLn
                    $  "define "
                    ++ Text.unpack name
                    ++ " := "
                    ++ show bodyTerm
                return $ s'
                    { envDefinitions = Map.insert name
                                                  bodyTerm
                                                  (envDefinitions s')
                    }
    Syntax.Assume ident ty -> do
        let name = unLoc (usage ident)
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
                putStrLn $ "assume " ++ Text.unpack name ++ " : " ++ show tyTerm
                return $ s'
                    { envAssumptions = Map.insert name
                                                  tyTerm
                                                  (envAssumptions s')
                    }
    Syntax.Prove ident ty -> do
        let name = unLoc (usage ident)
        putStrLn $ "Checking " ++ Text.unpack name
        result <- runTcM s $ do
            tyTerm  <- typeCheckExpr Empty [] ty
            tyTerm' <- reduce tyTerm
            α       <- freshMetavar (context tyTerm') tyTerm'
            search α
            checkSolved
            reduce α
        case result of
            Nothing -> do
                putStrLn $ "Error in " ++ Text.unpack name
                return s
            Just (bodyTerm, s') -> do
                putStrLn
                    $  "prove "
                    ++ Text.unpack name
                    ++ " := "
                    ++ show bodyTerm
                return $ s'
                    { envDefinitions = Map.insert name
                                                  bodyTerm
                                                  (envDefinitions s')
                    }

typeCheckExpr :: Context -> [Text] -> Expr N -> TcM Term
typeCheckExpr _Γ names = \case
    Syntax.Var _ n -> case n of
        -- We assume that name resolution is correct and the map lookups cannot fail.
        Local _ ident -> do
            let Just i = elemIndex (unLoc ident) names
            return (Var (fromDeBruijn _Γ i))
        Defined _ ident -> do
            definitions <- gets envDefinitions
            let Just body = Map.lookup (unLoc ident) definitions
            return (weakenGlobal _Γ body)
        Assumed _ ident -> do
            assumptions <- gets envAssumptions
            let Just _A = Map.lookup (unLoc ident) assumptions
            return (weakenGlobal _Γ (Assume (unLoc ident) Empty _A))
        Unbound ident -> fail $ "unbound name: " ++ Text.unpack (unLoc ident)
    Syntax.Hole _  -> typeCheckHole _Γ
    Syntax.Type _      -> return (Universe _Γ)
    Syntax.App _ f      args -> do
        f'    <- typeCheckExpr _Γ names f
        args' <- mapM (typeCheckExpr _Γ names) args
        typeCheckApp f' args'
    Syntax.Tuple _ args -> do
        args' <- mapM (typeCheckExpr _Γ names) args
        typeCheckTuple args'
    Syntax.Pi    _ params _B -> typeCheckPi _Γ names params _B
    Syntax.Lambda _ params b -> typeCheckLam _Γ names params b
    Syntax.Sigma _ params _B -> typeCheckSigma _Γ names params _B
    Syntax.Equal _ a b -> do
        f' <- typeCheckBuiltIn _Γ "Id"
        _A <- typeCheckHole _Γ
        a' <- typeCheckExpr _Γ names a
        b' <- typeCheckExpr _Γ names b
        typeCheckApp f' [_A, a', b']
    Syntax.Arrow _ _A     _B -> do
        _A' <- typeCheckExpr _Γ names _A
        checkIsType _A'
        _B' <- typeCheckExpr _Γ names _B
        checkIsType _B'
        return (Pi _A' (Apply (SubstWeaken _A') _B'))
    Syntax.Times _ _A     _B -> do
        _A' <- typeCheckExpr _Γ names _A
        _B' <- typeCheckExpr _Γ names _B
        f   <- typeCheckBuiltIn _Γ "Σ'"
        typeCheckApp f [_A', Lam _A' (Apply (SubstWeaken _A') _B')]

typeCheckPi :: Context -> [Text] -> [Param N] -> Expr N -> TcM Term
typeCheckPi _Γ names []                     _B = typeCheckExpr _Γ names _B
typeCheckPi _Γ names ((ident, _A) : params) _B = do
    let name = unLoc (usage ident)
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    _B' <- typeCheckPi (Extend _A') (name : names) params _B
    checkIsType _B'
    return (Pi _A' _B')

typeCheckLam :: Context -> [Text] -> [Param N] -> Expr N -> TcM Term
typeCheckLam _Γ names []                     b = typeCheckExpr _Γ names b
typeCheckLam _Γ names ((ident, _A) : params) b = do
    let name = unLoc (usage ident)
    _A' <- typeCheckExpr _Γ names _A
    checkIsType _A'
    b' <- typeCheckLam (Extend _A') (name : names) params b
    return (Lam _A' b')

typeCheckSigma :: Context -> [Text] -> [Param N] -> Expr N -> TcM Term
typeCheckSigma _Γ names []                     _B = typeCheckExpr _Γ names _B
typeCheckSigma _Γ names ((ident, _A) : params) _B = do
    let name = unLoc (usage ident)
    _A' <- typeCheckExpr _Γ names _A
    _B' <- typeCheckSigma (Extend _A') (name : names) params _B
    f   <- typeCheckBuiltIn _Γ "Σ'"
    typeCheckApp f [_A', Lam _A' _B']

typeCheckBuiltIn :: Context -> String -> TcM Term
typeCheckBuiltIn _Γ name = do
    let name' = Text.pack name
    assumptions <- gets envAssumptions
    case Map.lookup name' assumptions of
        Just _A -> return (weakenGlobal _Γ (Assume name' Empty _A))
        _       -> fail $ "can't find built-in: " ++ name

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
typeCheckApp f []           = return f
typeCheckApp f (arg : args) = do
    let _Γ = context f
    let _A = termType arg
    _B <- freshMetavar _Γ (Universe _Γ)
    unify (termType f) (Pi _A _B)
    typeCheckApp (App _A _B f arg) args

typeCheckTuple :: [Term] -> TcM Term
typeCheckTuple []       = error "typeCheckTuple: empty tuple"
typeCheckTuple [t     ] = return t
typeCheckTuple (a : ts) = do
    let _Γ  = context a
    let _A  = termType a
    let _Γ' = Extend _A
    _B   <- freshMetavar _Γ' (Universe _Γ')
    b    <- typeCheckTuple ts
    pair <- typeCheckBuiltIn _Γ "pair"
    typeCheckApp pair [_A, Lam _A _B, a, b]
