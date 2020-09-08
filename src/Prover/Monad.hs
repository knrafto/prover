-- | The main type-checking monad.
module Prover.Monad where

import Control.Exception
import Data.IORef

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)

import Control.Monad.Error.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class

import Prover.Syntax.Abstract
import Prover.Syntax.Internal
import Prover.Syntax.Position

-- | Read-only environment used for local variables.
data Env = Env
  { -- | List of local variable bindings in scope. Variables with no name are
    -- represented by `Nothing`.
    envVarNames :: [Maybe Name]
    -- | The current term context.
  , envCtx      :: Ctx
  } deriving (Show)

initialEnv :: Env
initialEnv = Env
  { envVarNames = []
  , envCtx      = C0
  }

-- | Global type-checking state.
data State = State
  { -- | For generating fresh NameIds.
    nextNameId        :: !NameId
    -- | For generating fresh MetaIds.
  , nextMetaId        :: !MetaId
    -- | Globally-defined names.
  , globalNames       :: HashMap Text NameId
    -- | Definitions.
  , defNames          :: HashMap NameId Name
  , defTypes          :: HashMap NameId Type
  , defTerms          :: HashMap NameId Term
    -- | Assumptions.
  , axiomNames        :: HashMap NameId Name
  , axiomTypes        :: HashMap NameId Type
    -- | Metavariables.
  , metaTypes         :: HashMap MetaId Type
  } deriving (Show)

initialState :: State
initialState = State
  { nextNameId        = NameId 0
  , nextMetaId        = MetaId 0
  , globalNames       = HashMap.empty
  , defNames          = HashMap.empty
  , defTypes          = HashMap.empty
  , defTerms          = HashMap.empty
  , axiomNames        = HashMap.empty
  , axiomTypes        = HashMap.empty
  , metaTypes         = HashMap.empty
  }

data Err
  -- | A name could not be resolved.
  = UnboundName Range Text
  -- | A built-in has not been defined.
  | MissingBuiltin Range Text
  -- | An expression cannot be applied to arguments.
  | CannotApply Expr
  -- | Some feature is currently unimplemented.
  | Unimplemented Range String
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

freshNameId :: M NameId
freshNameId = do
  s <- get
  let id = nextNameId s
  put s { nextNameId = succ id }
  return id

freshMetaId :: M MetaId
freshMetaId = do
  s <- get
  let id = nextMetaId s
  put s { nextMetaId = succ id }
  return id

lookupState :: (Eq k, Hashable k, Show k) => k -> (State -> HashMap k v) -> M v
lookupState k f = do
  m <- gets f
  case HashMap.lookup k m of
    Nothing -> error $ "lookup: " ++ show k
    Just v  -> return v