{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Monad where

import           Data.IORef
import           System.IO.Unsafe

import           Control.Monad.Except
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
    -- TODO: remove this field.
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

-- Runs a search, reporting any failure
runTcM :: TcM a -> IO (Either Diagnostic a)
runTcM (TcM m) = runExceptT (evalStateT m initialState)

{-# NOINLINE indentRef #-}
indentRef :: IORef Int
indentRef = unsafePerformIO (newIORef 0)

trace :: MonadIO m => String -> m a -> m a
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

throwDiagnostic :: MonadError Diagnostic m => Range -> String -> m a
throwDiagnostic r s = throwError (Diagnostic r s)

-- Generate a new metavariable for the given context Γ and type A. The new meta
-- has type α : Γ → A and the returned term is α Γ.
freshMeta :: (MonadState TcState m, MonadIO m) => Ctx -> Type -> m Term
freshMeta ctx _A = do
    i <- gets tcNextId
    let m = MetaId i
    let ty = ctxPi ctx _A
    modify $ \s -> s { tcNextId = i + 1, tcMetaTypes = HashMap.insert m ty (tcMetaTypes s) }
    let t = Meta m (ctxVars ctx)
    trace ("Creating meta " ++ show t) $ return t
