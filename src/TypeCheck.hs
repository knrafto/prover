{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module TypeCheck where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.IORef
import           Data.List
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           System.IO.Unsafe

import qualified Flags
import           Location
import           Naming
import           Syntax                         ( Id
                                                , Ann
                                                , ann
                                                , Expr
                                                , Param
                                                , Statement
                                                )
import qualified Syntax
import           Term

data TcAnn = TcAnn Range Term

data Tc
type instance Id Tc = Name
type instance Ann Tc = TcAnn

exprTerm :: Expr Tc -> Term
exprTerm e = case ann e of
    TcAnn _ t -> t

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

newtype TcM a = TcM { unTcM :: StateT TcState (ExceptT String IO) a }
    deriving (Functor, Applicative, Monad, MonadIO, MonadError String, MonadState TcState)

{-# NOINLINE indentRef #-}
indentRef :: IORef Int
indentRef = unsafePerformIO (newIORef 0)

trace :: String -> TcM a -> TcM a
trace e m = do
    liftIO $ do
        level <- readIORef indentRef
        writeIORef indentRef (level + 1)
        let pad = replicate (2 * level) ' '
        when Flags.print_trace $
            putStrLn $ unlines $ map (pad ++) $ lines e
    a <- m
    liftIO $ do
        level <- readIORef indentRef
        writeIORef indentRef (level - 1)
    return a

-- Runs a search, reporting any failure
runTcM :: TcM a -> IO (Either String (a, TcState))
runTcM (TcM m) = runExceptT (runStateT m initialState)

-- Generate a metavar for the given context and type.
freshMetavar :: Context -> Term -> TcM Term
freshMetavar _Γ _A = do
    i <- gets nextId
    modify $ \s -> s { nextId = i + 1 }
    return $ Metavar (VarId i) _Γ _A

-- Generate an unknown term and type.
hole :: Context -> TcM Term
hole _Γ = do
    -- We generate variables for both the hole itself, and its type. Luckily
    -- for now we don't have to do this forever, since the type of any type is
    -- the universe.
    _A <- freshMetavar _Γ (Universe _Γ)
    freshMetavar _Γ _A

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
    throwError
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

typeCheck :: [Statement N] -> TcM [Statement Tc]
typeCheck = mapM typeCheckStatement

typeCheckStatement :: Statement N -> TcM (Statement Tc)
typeCheckStatement = \case
    Syntax.Define n mty body -> do
        let name = unLoc (nameUsage n)
        body' <- typeCheckExpr Empty [] body
        mty' <- case mty of
            Nothing -> return Nothing
            Just ty -> do
                ty' <- typeCheckExpr Empty [] ty
                unify (termType (exprTerm body')) (exprTerm ty')
                return (Just ty')
        checkSolved
        modify $ \s -> s { envDefinitions = Map.insert name (exprTerm body') (envDefinitions s) }
        return (Syntax.Define n mty' body')
    Syntax.Assume n ty -> do
        let name = unLoc (nameUsage n)
        ty' <- typeCheckExpr Empty [] ty
        checkSolved
        modify $ \s -> s { envAssumptions = Map.insert name (exprTerm ty') (envAssumptions s) }
        return (Syntax.Assume n ty')
    Syntax.Prove _ _ -> fail "prove not implemented"

typeCheckExpr :: Context -> [Text] -> Expr N -> TcM (Expr Tc)
typeCheckExpr _Γ names = \case
    Syntax.Var l n -> do
        let name = unLoc (nameUsage n)
        -- We assume that name resolution is correct and the map lookups cannot fail.
        t <- case nameKind n of
            Local -> do
                let Just i = elemIndex name names
                return (Var (fromDeBruijn _Γ i))
            Defined -> do
                definitions <- gets envDefinitions
                let Just body = Map.lookup name definitions
                return (weakenGlobal _Γ body)
            Assumed -> do
                assumptions <- gets envAssumptions
                let Just _A = Map.lookup name assumptions
                return (weakenGlobal _Γ (Assume name Empty _A))
            Unbound ->
                fail $ "unbound name: " ++ Text.unpack name
        return (Syntax.Var (TcAnn l t) n)
    Syntax.Hole l -> do
        t <- hole _Γ
        return (Syntax.Hole (TcAnn l t))
    Syntax.Type l       -> return (Syntax.Type (TcAnn l (Universe _Γ)))
    Syntax.App l f arg -> do
        f'    <- typeCheckExpr _Γ names f
        arg'  <- typeCheckExpr _Γ names arg
        t     <- typeCheckApp (exprTerm f') (exprTerm arg')
        return (Syntax.App (TcAnn l t) f' arg')
    Syntax.Tuple l args -> do
        args' <- mapM (typeCheckExpr _Γ names) args
        t     <- typeCheckTuple (map exprTerm args')
        return (Syntax.Tuple (TcAnn l t) args')
    Syntax.Pi l param body -> do
        (param', paramTerm, body') <- typeCheckParam _Γ names param body
        t <- typeCheckPi paramTerm (exprTerm body')
        return (Syntax.Pi (TcAnn l t) param' body')
    Syntax.Lambda l param body -> do
        (param', paramTerm, body') <- typeCheckParam _Γ names param body
        t <- typeCheckLambda paramTerm (exprTerm body')
        return (Syntax.Lambda (TcAnn l t) param' body')
    Syntax.Sigma  l param body -> do
        (param', paramTerm, body') <- typeCheckParam _Γ names param body
        t <- typeCheckSigma paramTerm (exprTerm body')
        return (Syntax.Sigma (TcAnn l t) param' body')
    Syntax.Equal  l a      b  -> do
        f' <- builtin _Γ "Id"
        _A <- hole _Γ
        a' <- typeCheckExpr _Γ names a
        b' <- typeCheckExpr _Γ names b
        t  <- typeCheckApps f' [_A, exprTerm a', exprTerm b']
        return (Syntax.Equal (TcAnn l t) a' b')
    Syntax.Arrow l a b -> do
        a' <- typeCheckExpr _Γ names a
        b' <- typeCheckExpr _Γ names b
        let _A = exprTerm a'
        let _B = exprTerm b'
        checkIsType _A
        checkIsType _B
        let t = Pi _A (Apply (SubstWeaken _A) _B)
        return (Syntax.Arrow (TcAnn l t) a' b')
    Syntax.Times l a b -> do
        a' <- typeCheckExpr _Γ names a
        b' <- typeCheckExpr _Γ names b
        let _A = exprTerm a'
        let _B = exprTerm b'
        f   <- builtin _Γ "Σ'"
        t <- typeCheckApps f [_A, Lam _A (Apply (SubstWeaken _A) _B)]
        return (Syntax.Times (TcAnn l t) a' b')

builtin :: Context -> String -> TcM Term
builtin _Γ name = do
    let name' = Text.pack name
    assumptions <- gets envAssumptions
    case Map.lookup name' assumptions of
        Just _A -> return (weakenGlobal _Γ (Assume name' Empty _A))
        _       -> fail $ "can't find built-in: " ++ name

checkIsType :: Term -> TcM ()
checkIsType t = unify (termType t) (Universe (context t))

typeCheckParam :: Context -> [Text] -> Param N -> Expr N -> TcM (Param Tc, Term, Expr Tc)
typeCheckParam _Γ names (n, me) body = do
    let name = unLoc (nameUsage n)
    (me', t) <- case me of
        Nothing -> do
            t <- hole _Γ
            return (Nothing, t)
        Just e -> do
            e' <- typeCheckExpr _Γ names e
            return (Just e', exprTerm e')
    body' <- typeCheckExpr (Extend t) (name : names) body
    return ((n, me'), t, body')

typeCheckPi :: Term -> Term -> TcM Term
typeCheckPi _A _B = do
    checkIsType _A
    checkIsType _B
    return (Pi _A _B)

typeCheckLambda :: Term -> Term -> TcM Term
typeCheckLambda _A _B = do
    checkIsType _A
    return (Lam _A _B)

typeCheckSigma :: Term -> Term -> TcM Term
typeCheckSigma _A _B = do
    f <- builtin (context _A) "Σ'"
    typeCheckApps f [_A, Lam _A _B]

typeCheckApp :: Term -> Term -> TcM Term
typeCheckApp f arg = do
    let _Γ = context f
    let _A = termType arg
    _B <- freshMetavar _Γ (Universe _Γ)
    unify (termType f) (Pi _A _B)
    return (App _A _B f arg)

typeCheckApps :: Term -> [Term] -> TcM Term
typeCheckApps f []           = return f
typeCheckApps f (arg : args) = do
    f' <- typeCheckApp f arg
    typeCheckApps f' args

typeCheckTuple :: [Term] -> TcM Term
typeCheckTuple []       = error "typeCheckTuple: empty tuple"
typeCheckTuple [t     ] = return t
typeCheckTuple (a : ts) = do
    let _Γ  = context a
    let _A  = termType a
    let _Γ' = Extend _A
    _B   <- freshMetavar _Γ' (Universe _Γ')
    b    <- typeCheckTuple ts
    pair <- builtin _Γ "pair"
    typeCheckApps pair [_A, Lam _A _B, a, b]

printStatements :: [Statement Tc] -> IO ()
printStatements = mapM_ printStatement

printStatement :: Statement Tc -> IO ()
printStatement = \case
    Syntax.Define n _ body -> do
        let name = unLoc (nameUsage n)
        putStrLn $ "define " ++ Text.unpack name ++ " := " ++ show (exprTerm body)
    Syntax.Assume n ty -> do
        let name = unLoc (nameUsage n)
        putStrLn $ "assume " ++ Text.unpack name ++ " : " ++ show (exprTerm ty)
    Syntax.Prove _ _ -> fail "prove not implemented"
