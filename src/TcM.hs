{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TcM where

import           Data.IORef
import           System.IO.Unsafe

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Text                      ( Text )

import Flags
import Term

-- TODO: use HashMap
data TcState = TcState
    -- Global definitions, and their values.
    { tcDefinitions :: Map Text (Term, Type)
    -- Global assumptions, and their types.
    , tcAssumptions :: Map Text Term
    -- Next metavar id.
    , tcNextId :: !Int
    -- Metavar types.
    , tcMetaTypes :: Map MetaId Type
    -- Metavar substitution.
    , tcMetaValues :: Map MetaId Term
    -- Unsolved unification equations.
    , tcUnsolvedEquations :: [(Ctx, Term, Term)]
    }

initialState :: TcState
initialState = TcState { tcDefinitions       = Map.empty
                       , tcAssumptions       = Map.empty
                       , tcNextId            = 0
                       , tcMetaTypes         = Map.empty
                       , tcMetaValues        = Map.empty
                       , tcUnsolvedEquations = []
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

-- Generate a new metavariable for the given context Γ and type A. The new meta
-- has type α : Γ → A and the returned term is α Γ.
freshMeta :: Ctx -> Type -> TcM Term
freshMeta ctx _A = do
    i <- gets tcNextId
    let m = MetaId i
    let ty = ctxPi ctx _A
    modify $ \s -> s { tcNextId = i + 1, tcMetaTypes = Map.insert m ty (tcMetaTypes s) }
    return (Meta m (ctxVars ctx))

saveEquation :: Ctx -> Term -> Term -> TcM ()
saveEquation ctx t1 t2 =
    modify $ \s -> s { tcUnsolvedEquations = (ctx, t1, t2) : tcUnsolvedEquations s }

-- TODO: occurs check
assign :: MetaId -> Term -> TcM ()
assign i t = do
    trace ("Assigning " ++ show i ++ " ↦ " ++ show t) $ return ()
    eqs <- gets tcUnsolvedEquations
    modify $ \s ->
        s { tcMetaValues = Map.insert i t (tcMetaValues s), tcUnsolvedEquations = [] }
    unless (null eqs) $ trace "Retrying unsolved equations" $ forM_
        eqs
        (\(ctx, t1, t2) -> unify ctx t1 t2)

unificationFailure :: Ctx -> Term -> Term -> TcM a
unificationFailure ctx t1 t2 =
    throwError
        $  "Failed to unify in context: "
        ++ show ctx
        ++ "\n"
        ++ "  "
        ++ show t1
        ++ "\n"
        ++ "  "
        ++ show t2

checkSolved :: TcM ()
checkSolved = do
    eqs <- gets tcUnsolvedEquations
    modify $ \s -> s { tcUnsolvedEquations = [] }
    case eqs of
        []             -> return ()
        ((ctx, t1, t2) : _) -> unificationFailure ctx t1 t2

unify :: Ctx -> Term -> Term -> TcM ()
unify ctx t1 t2 = do
    t1' <- whnf ctx t1
    t2' <- whnf ctx t2
    trace
            (  "Unifying in context: "
            ++ show ctx
            ++ "\n  "
            ++ show t1'
            ++ "\n  "
            ++ show t2'
            )
        $ unify' ctx t1' t2'

unify' :: Ctx -> Term -> Term -> TcM ()
unify' ctx t1 t2 = case (t1, t2) of
    -- TODO: flex-flex
    (Meta _ _, Meta _ _) -> saveEquation ctx t1 t2
    (Meta m args, t) -> unifyMeta ctx m args t
    (t, Meta m args) -> unifyMeta ctx m args t
    (Var i1 args1, Var i2 args2)
        | i1 == i2 && length args1 == length args2 -> zipWithM_ (unify ctx) args1 args2
    (Assumption i1 args1, Assumption i2 args2)
        | i1 == i2 && length args1 == length args2 -> zipWithM_ (unify ctx) args1 args2
    -- TODO: lam
    (Universe, Universe) -> return ()
    (Pi _A1 _B1, Pi _A2 _B2) -> do
        unify ctx _A1 _A2
        unify (ExtendCtx ctx _A1) _B1 _B2
    _ -> unificationFailure ctx t1 t2

unifyMeta :: Ctx -> MetaId -> [Term] -> Term -> TcM ()
unifyMeta ctx m args t
    -- e.g. ?m v₂ v₁ v₀ = t  =>  ?m = λ λ λ t
    | args == ctxVars ctx = assign m (makeLam ctx t)
    | otherwise = saveEquation ctx (Meta m args) t
  where
    makeLam EmptyCtx t' = t'
    makeLam (ExtendCtx ctx' _) t' = makeLam ctx' (Lam t')

-- Attempts to simplify a term to a weak head normal form.
whnf :: Ctx -> Term -> TcM Term
whnf ctx t = case t of
    Meta m args -> do
        metaValues <- gets tcMetaValues
        -- TODO: path compression
        case Map.lookup m metaValues of
            Nothing -> return t
            Just t' -> return (app (weakenGlobal ctx t') args)
    _ -> return t
