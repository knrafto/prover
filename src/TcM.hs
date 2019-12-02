{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TcM where

import           Data.IORef
import           System.IO.Unsafe

import           Control.Monad.Except
import           Control.Monad.Fail
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
    , tcUnsolvedEquations :: [(Ctx, Type, Term, Term)]
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
    deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadError String, MonadState TcState)

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

saveEquation :: Ctx -> Type -> Term -> Term -> TcM ()
saveEquation ctx ty t1 t2 =
    modify $ \s -> s { tcUnsolvedEquations = (ctx, ty, t1, t2) : tcUnsolvedEquations s }

-- TODO: occurs check
assign :: MetaId -> Term -> TcM ()
assign i t = do
    trace ("Assigning " ++ show i ++ " ↦ " ++ show t) $ return ()
    eqs <- gets tcUnsolvedEquations
    modify $ \s ->
        s { tcMetaValues = Map.insert i t (tcMetaValues s), tcUnsolvedEquations = [] }
    unless (null eqs) $ trace "Retrying unsolved equations" $ forM_
        eqs
        (\(ctx, ty, t1, t2) -> unify ctx ty t1 t2)

unificationFailure :: Ctx -> Type -> Term -> Term -> TcM a
unificationFailure ctx _ t1 t2 =
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
        ((ctx, ty, t1, t2) : _) -> unificationFailure ctx ty t1 t2

unify :: Ctx -> Type -> Term -> Term -> TcM ()
unify ctx ty t1 t2 = do
    ty' <- whnf ctx ty
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
        $ unify' ctx ty' t1' t2'

unify' :: Ctx -> Type -> Term -> Term -> TcM ()
unify' ctx ty t1 t2 = case (ty, t1, t2) of
    -- TODO: flex-flex
    (_, Meta _ _, Meta _ _) -> saveEquation ctx ty t1 t2
    (_, Meta m args, t) -> unifyMeta ctx ty m args t
    (_, t, Meta m args) -> unifyMeta ctx ty m args t
    (_, Var i1 args1, Var i2 args2)
        | i1 == i2 && length args1 == length args2 ->
            unifySpine ctx (ctxVarType ctx i1) (zip args1 args2)
    (_, Assumption n1 args1, Assumption n2 args2)
        | n1 == n2 && length args1 == length args2 -> do
            assumptions <- gets tcAssumptions
            let Just nty = Map.lookup n1 assumptions
            unifySpine ctx (weakenGlobal ctx nty) (zip args1 args2)
    -- TODO: eta
    (Pi _A _B, Lam b1, Lam b2) -> unify (ExtendCtx ctx _A) _B b1 b2
    (Universe, Universe, Universe) -> return ()
    (Universe, Pi _A1 _B1, Pi _A2 _B2) -> do
        unify ctx Universe _A1 _A2
        unify (ExtendCtx ctx _A1) Universe _B1 _B2
    _ -> unificationFailure ctx ty t1 t2

unifyMeta :: Ctx -> Type -> MetaId -> [Term] -> Term -> TcM ()
unifyMeta ctx ty m args t
    -- e.g. ?m v₂ v₁ v₀ = t  =>  ?m = λ λ λ t
    | args == ctxVars ctx = assign m (makeLam ctx t)
    | otherwise = saveEquation ctx ty (Meta m args) t
  where
    makeLam EmptyCtx t' = t'
    makeLam (ExtendCtx ctx' _) t' = makeLam ctx' (Lam t')

unifySpine :: Ctx -> Type -> [(Term, Term)] -> TcM ()
unifySpine _ _ [] = return ()
unifySpine ctx hty ((arg1, arg2) : args) = do
    Pi _A _B <- whnf ctx hty
    unify ctx _A arg1 arg2
    unifySpine ctx (instantiate _B arg1) args 

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
