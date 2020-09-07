-- | The main type-checking monad.
module Prover.Monad where

import Control.Exception
import Data.IORef

import Data.Text (Text)

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class

import Prover.Syntax.Internal
import Prover.Syntax.Position

-- | Read-only environment used for local variables.
data Env = Env
  { 
  } deriving (Show)

initialEnv :: Env
initialEnv = Env
  {}

-- | Global type-checking state.
data State = State
  { -- | For generating fresh NameIds.
    nextNameId :: !NameId
    -- | For generating fresh MetaIds.
  , nextMetaId :: !MetaId
  } deriving (Show)

initialState :: State
initialState = State
  { nextNameId = NameId 0
  , nextMetaId = MetaId 0
  }

data Err
  -- | A name could not be resolved.
  = UnboundName Range Text
  deriving (Show)

instance Exception Err

newtype M a = M { unM :: IORef State -> Env -> IO a }

-- TODO: benchmark inlining all of these

instance Functor M where
  fmap f (M m) = M $ \r e -> fmap f (m r e)

instance Applicative M where
  pure a        = M $ \_ _ -> return a
  M mf <*> M ma = M $ \r e -> mf r e <*> ma r e

instance Monad M where
  M m >>= k = M $ \r e -> m r e >>= \a -> unM (k a) r e

instance MonadIO M where
  liftIO m = M $ \_ _ -> m

instance MonadReader Env M where
  ask           = M $ \_ e -> return e
  local f (M m) = M $ \r e -> m r (f e)

instance MonadState State M where
  get   = M $ \r _ -> liftIO (readIORef r)
  put s = M $ \r _ -> liftIO (writeIORef r s)

instance MonadError Err M where
  throwError err = liftIO (throwIO err)
  catchError m h = M $ \r e ->  unM m r e `catch` \err -> unM (h err) r e

runM :: M a -> IO (Either Err a)
runM (M m) = do
  r <- newIORef initialState
  let e = initialEnv
  (Right <$> m r e) `catch` \err -> return (Left err)

debug :: String -> M ()
debug = liftIO . putStrLn

freshNameId :: M NameId
freshNameId = do
  s <- get
  let nameId = nextNameId s
  put s { nextNameId = succ nameId }
  return nameId

freshMetaId :: M MetaId
freshMetaId = do
  s <- get
  let metaId = nextMetaId s
  put s { nextMetaId = succ metaId }
  return metaId
