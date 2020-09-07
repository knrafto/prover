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

data TCEnv = TCEnv
  { 
  } deriving (Show)

initialEnv :: TCEnv
initialEnv = TCEnv
  {}

data TCState = TCState
  { -- | For generating fresh NameIds.
    nextNameId :: !NameId
    -- | For generating fresh MetaIds.
  , nextMetaId :: !MetaId
  } deriving (Show)

initialState :: TCState
initialState = TCState
  { nextNameId = NameId 0
  , nextMetaId = MetaId 0
  }

data TCError
  -- | A name could not be resolved.
  = UnboundName Range Text
  deriving (Show)

instance Exception TCError

newtype TCM a = TCM { unTCM :: IORef TCState -> TCEnv -> IO a }

-- TODO: benchmark inlining all of these

instance Functor TCM where
  fmap f (TCM m) = TCM $ \r e -> fmap f (m r e)

instance Applicative TCM where
  pure a            = TCM $ \_ _ -> return a
  TCM mf <*> TCM ma = TCM $ \r e -> mf r e <*> ma r e

instance Monad TCM where
  TCM m >>= k = TCM $ \r e -> m r e >>= \a -> unTCM (k a) r e

instance MonadIO TCM where
  liftIO m = TCM $ \_ _ -> m

instance MonadReader TCEnv TCM where
  ask             = TCM $ \_ e -> return e
  local f (TCM m) = TCM $ \r e -> m r (f e)

instance MonadState TCState TCM where
  get   = TCM $ \r _ -> liftIO (readIORef r)
  put s = TCM $ \r _ -> liftIO (writeIORef r s)

instance MonadError TCError TCM where
  throwError err = liftIO (throwIO err)
  catchError m h = TCM $ \r e ->  unTCM m r e `catch` \err -> unTCM (h err) r e

runTCM :: TCM a -> IO (Either TCError a)
runTCM (TCM m) = do
  r <- newIORef initialState
  let e = initialEnv
  (Right <$> m r e) `catch` \err -> return (Left err)

debug :: String -> TCM ()
debug = liftIO . putStrLn

freshNameId :: TCM NameId
freshNameId = do
  s <- get
  let nameId = nextNameId s
  put s { nextNameId = succ nameId }
  return nameId

freshMetaId :: TCM MetaId
freshMetaId = do
  s <- get
  let metaId = nextMetaId s
  put s { nextMetaId = succ metaId }
  return metaId
