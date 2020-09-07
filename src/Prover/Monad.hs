-- | The main type-checking monad.
module Prover.Monad where

import Control.Exception
import Data.IORef

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class

import qualified Prover.Syntax.Abstract as A
import Prover.Syntax.Position

data TCEnv = TCEnv
  { -- | All variables in scope and their bindings.
    tcScope :: HashMap Text A.Binding
  } deriving (Show)

initialEnv :: TCEnv
initialEnv = TCEnv
  { tcScope = HashMap.empty
  }

data TCState = TCState
  { -- | For generating fresh NameIds.
    nextNameId :: !A.NameId
  } deriving (Show)

initialState :: TCState
initialState = TCState
  { nextNameId = A.NameId 0
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

freshNameId :: TCM A.NameId
freshNameId = do
  s <- get
  let nameId = nextNameId s
  put s { nextNameId = succ nameId }
  return nameId
