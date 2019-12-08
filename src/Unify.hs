{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Unify where

import           Data.IORef
import           Data.List
import           System.IO.Unsafe

import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.Trans.Maybe
import           Control.Monad.State
import           Data.HashMap.Strict            ( HashMap )
import qualified Data.HashMap.Strict           as HashMap
import           Data.Text                      ( Text )

import Diagnostic
import Flags
import Location
import Term

-- A term annotated with a type, used for type-checking and unification.
type UTerm = (Term, Type)

data TcState = TcState
    -- Global definitions, and their values.
    { tcDefinitions :: HashMap Text UTerm
    -- Global assumptions, and their types.
    , tcAssumptions :: HashMap Text Type
    -- Next metavar id.
    , tcNextId :: !Int
    -- Metavar types.
    , tcMetaTypes :: HashMap MetaId Type
    -- Metavar substitution.
    , tcMetaValues :: HashMap MetaId Term
    -- Unsolved unification equations.
    , tcUnsolvedEquations :: [(Range, Ctx, Type, Term, Term)]
    }

initialState :: TcState
initialState = TcState { tcDefinitions       = HashMap.empty
                       , tcAssumptions       = HashMap.empty
                       , tcNextId            = 0
                       , tcMetaTypes         = HashMap.empty
                       , tcMetaValues        = HashMap.empty
                       , tcUnsolvedEquations = []
                       }

newtype TcM a = TcM { unTcM :: StateT TcState (ExceptT Diagnostic IO) a }
    deriving (Functor, Applicative, Monad, MonadFail, MonadIO, MonadError Diagnostic, MonadState TcState)

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

throwDiagnostic :: Range -> String -> TcM a
throwDiagnostic r s = throwError (Diagnostic r s)

-- Runs a search, reporting any failure
runTcM :: TcM a -> IO (Either Diagnostic (a, TcState))
runTcM (TcM m) = runExceptT (runStateT m initialState)

-- Generate a new metavariable for the given context Γ and type A. The new meta
-- has type α : Γ → A and the returned term is α Γ.
freshMeta' :: Ctx -> Type -> TcM Term
freshMeta' ctx _A = do
    i <- gets tcNextId
    let m = MetaId i
    let ty = ctxPi ctx _A
    modify $ \s -> s { tcNextId = i + 1, tcMetaTypes = HashMap.insert m ty (tcMetaTypes s) }
    let t = Meta m (ctxVars ctx)
    trace ("Creating meta " ++ show t) $ return t

saveEquation :: Range -> Ctx -> Type -> Term -> Term -> TcM ()
saveEquation l ctx ty t1 t2 =
    modify $ \s -> s { tcUnsolvedEquations = (l, ctx, ty, t1, t2) : tcUnsolvedEquations s }

-- TODO: occurs check
assign :: MetaId -> Term -> TcM ()
assign i t = do
    trace ("Assigning " ++ show i ++ " ↦ " ++ show t) $ return ()
    eqs <- gets tcUnsolvedEquations
    modify $ \s ->
        s { tcMetaValues = HashMap.insert i t (tcMetaValues s), tcUnsolvedEquations = [] }
    unless (null eqs) $ trace "Retrying unsolved equations" $ forM_
        eqs
        (\(l, ctx, ty, t1, t2) -> unify l ctx ty t1 t2)

unificationFailure :: Range -> Ctx -> Type -> Term -> Term -> TcM a
unificationFailure l ctx _ t1 t2 =
    throwDiagnostic l
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
        [] -> return ()
        ((l, ctx, ty, t1, t2) : _) -> unificationFailure l ctx ty t1 t2

unify :: Range -> Ctx -> Type -> Term -> Term -> TcM ()
unify l ctx ty t1 t2 = do
    ty' <- whnf ty
    t1' <- whnf t1
    t2' <- whnf t2
    -- TODO: include Range in trace
    trace
            (  "Unifying in context: "
            ++ show ctx
            ++ "\n  "
            ++ show t1'
            ++ "\n  "
            ++ show t2'
            )
        $ unify' l ctx ty' t1' t2'

unify' :: Range -> Ctx -> Type -> Term -> Term -> TcM ()
unify' l ctx ty t1 t2 = case (ty, t1, t2) of
    -- TODO: flex-flex
    (_, Meta _ _, Meta _ _) -> saveEquation l ctx ty t1 t2
    (_, Meta m args, t) -> unifyMeta l ctx ty m args t
    (_, t, Meta m args) -> unifyMeta l ctx ty m args t
    (_, Var i1 args1, Var i2 args2)
        | i1 == i2 && length args1 == length args2 ->
            unifySpine l ctx (ctxVarType ctx i1) (zip args1 args2)
    (_, Assumption n1 args1, Assumption n2 args2)
        | n1 == n2 && length args1 == length args2 -> do
            assumptions <- gets tcAssumptions
            let Just nty = HashMap.lookup n1 assumptions
            unifySpine l ctx nty (zip args1 args2)
    (Pi _A _B, Lam b1, Lam b2) -> unify l (ctx :> _A) _B b1 b2
    -- η-expansion
    (Pi _A _B, Lam b, t) -> unify l (ctx :> _A) _B b (app (weaken t) [Var 0 []])
    (Pi _A _B, t, Lam b) -> unify l (ctx :> _A) _B (app (weaken t) [Var 0 []]) b
    (Universe, Universe, Universe) -> return ()
    (Universe, Pi _A1 _B1, Pi _A2 _B2) -> do
        unify l ctx Universe _A1 _A2
        unify l (ctx :> _A1) Universe _B1 _B2
    _ -> unificationFailure l ctx ty t1 t2

-- TODO: pruning
unifyMeta :: Range -> Ctx -> Type -> MetaId -> [Term] -> Term -> TcM ()
unifyMeta l ctx ty m args t = do
    result <- runMaybeT $ do
        σ <- convertMetaArgs args
        invertVarSubst σ t
    case result of
        Nothing -> saveEquation l ctx ty (Meta m args) t
        Just t' -> assign m (makeLam (length args) t')
  where
    makeLam 0 t' = t'
    makeLam n t' = makeLam (n - 1) (Lam t')

unifySpine :: Range -> Ctx -> Type -> [(Term, Term)] -> TcM ()
unifySpine _ _ _ [] = return ()
unifySpine l ctx hty ((arg1, arg2) : args) = do
    Pi _A _B <- whnf hty
    unify l ctx _A arg1 arg2
    unifySpine l ctx (instantiate _B arg1) args 

-- Attempts to simplify a term to a weak head normal form.
whnf :: Term -> TcM Term
whnf t = case t of
    Meta m args -> do
        metaValues <- gets tcMetaValues
        -- TODO: path compression
        case HashMap.lookup m metaValues of
            Nothing -> return t
            Just t' -> return (app t' args)
    _ -> return t

-- A variable substitution, represented as a list of de Bruijn indices. Note
-- that this may seem reversed, since index zero is written on the left for
-- lists but on the right in contexts.
-- TODO: use strict list
type VarSubst = [Int]

-- An analogue of SubstLift. liftVarSubst σ acts like the identity on var 0,
-- and like σ on other vars.
liftVarSubst :: VarSubst -> VarSubst
liftVarSubst σ = 0 : map (+ 1) σ

-- Determine if a series of arguments (to a meta) is a variable substitution.
convertMetaArgs :: [Term] -> MaybeT TcM VarSubst
convertMetaArgs args = mapM convertMetaArg (reverse args)
  where
    convertMetaArg t = do
        t' <- lift $ whnf t
        case t' of
            Var i [] -> return i
            _ -> mzero

-- invertVarSubst σ t tries to find a unique term u such that u[σ] = t.
invertVarSubst :: VarSubst -> Term -> MaybeT TcM Term
invertVarSubst σ t = do
    t' <- lift $ whnf t
    case t' of
        Meta m args -> Meta m <$> mapM (invertVarSubst σ) args
        Var i args -> case elemIndices i σ of
            [i'] -> Var i' <$> mapM (invertVarSubst σ) args
            _ -> mzero
        Assumption n args -> Assumption n <$> mapM (invertVarSubst σ) args
        Lam b -> Lam <$> invertVarSubst (liftVarSubst σ) b
        Universe -> return Universe
        Pi a b -> Pi <$> invertVarSubst σ a <*> invertVarSubst (liftVarSubst σ) b
