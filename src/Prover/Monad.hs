-- | The main type-checking monad.
module Prover.Monad where

import Control.Exception
import Data.IORef

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class

data TCEnv = TCEnv

data TCState = TCState

data TCErr = TCErr
  deriving (Show)

instance Exception TCErr

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

instance MonadError TCErr TCM where
  throwError err = liftIO (throwIO err)
  catchError m h = TCM $ \r e ->  unTCM m r e `catch` \err -> unTCM (h err) r e

debug :: String -> TCM ()
debug = liftIO . putStrLn
