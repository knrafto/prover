-- | The main type-checking monad.
module Prover.Monad where

import Data.IORef

import Data.Hashable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Text (Text)

import Control.Monad.IO.Class
import Control.Monad.State.Class

import Prover.Pattern
import Prover.Syntax.Abstract
import Prover.Syntax.Position
import Prover.Term

data Error
  -- | A name could not be resolved.
  = UnboundName Range Text
  -- | A false constraint.
  -- TODO: add more info
  | TypeError Range
  -- | An unsolved constraint.
  -- TODO: add more info
  | UnsolvedConstraint Range
  -- | An unsolved meta.
  | UnsolvedMeta Range MetaId
  -- | An expression that can't be used as a pattern.
  | BadPattern Range
  -- | Some parameter can't be determined by the pattern.
  | MissingPatternVariable Range
  -- | An implicit parameter that doesn't appear at the front.
  | LateImplicitParam Range Param
  deriving (Show)

-- | Constraints for unification.
data Constraint
  -- TODO: split into two constructors? "trivial", "inconsistent"
  = Solved Bool
  | TermEq Ctx Type Term Term
  | SpineEq Ctx Type [(Term, Term)]
  | And [Constraint]
  | ExactlyOne [Constraint]
  | Guarded Constraint Constraint
  deriving (Show)

-- | A "user-facing" constraint as a result of typechecking.
data Equation = Equation Range Constraint
  deriving (Show)

-- | Global type-checking state.
data State = State
  { -- | Error messages.
    errors            :: [Error]
    -- | For generating fresh NameIds.
  , nextNameId        :: !NameId
    -- | For generating fresh MetaIds.
  , nextMetaId        :: !MetaId
    -- | Fixity declarations.
  , fixities          :: HashMap Text (Fixity, Int)
    -- | Globally-defined names.
  , globalNames       :: HashMap Text NameId
    -- | Definitions. TODO: use a record?
  , defNames          :: HashMap NameId Name
  , defImplicits      :: HashMap NameId Int
  , defTypes          :: HashMap NameId Type
  , defTerms          :: HashMap NameId Term
    -- | Axioms. TODO: use a record?
  , axiomNames        :: HashMap NameId Name
  , axiomImplicits    :: HashMap NameId Int
  , axiomTypes        :: HashMap NameId Type
  , axiomRules        :: HashMap NameId [Rule]
    -- | Metavariables. TODO: use a record?
  , metaRanges        :: HashMap MetaId Range
  , metaTypes         :: HashMap MetaId Type
  , metaTerms         :: HashMap MetaId Term
    -- | Unsolved metavariables for the current definition, for tracking errors.
    -- If unification fails, there may be metas that are not "unsolved" yet do
    -- not have a term assigned, but we don't want to emit an error about these
    -- metas again.
  , unsolvedMetas     :: HashSet MetaId
    -- | Type-checking constraints.
  , equations         :: [Equation]
  } deriving (Show)

initialState :: State
initialState = State
  { errors            = []
  , nextNameId        = NameId 0
  , nextMetaId        = MetaId 0
  , fixities          = HashMap.empty
  , globalNames       = HashMap.empty
  , defNames          = HashMap.empty
  , defImplicits      = HashMap.empty
  , defTypes          = HashMap.empty
  , defTerms          = HashMap.empty
  , axiomNames        = HashMap.empty
  , axiomImplicits    = HashMap.empty
  , axiomTypes        = HashMap.empty
  , axiomRules        = HashMap.empty
  , metaRanges        = HashMap.empty
  , metaTypes         = HashMap.empty
  , metaTerms         = HashMap.empty
  , unsolvedMetas     = HashSet.empty
  , equations         = []
  }

newtype M a = M { unM :: IORef State -> IO a }

-- TODO: benchmark inlining all of these

instance Functor M where
  fmap f (M m) = M $ \r -> fmap f (m r)

instance Applicative M where
  pure a        = M $ \_ -> return a
  M mf <*> M ma = M $ \r -> mf r <*> ma r

instance Monad M where
  M m >>= k = M $ \r -> m r >>= \a -> unM (k a) r

instance MonadIO M where
  liftIO m = M $ \_ -> m

instance MonadState State M where
  get   = M $ \r -> liftIO (readIORef r)
  put s = M $ \r -> liftIO (writeIORef r s)

runM :: M a -> IO (a, State)
runM (M m) = do
  r <- newIORef initialState
  a <- m r
  s <- readIORef r
  return (a, s)

emitError :: Error -> M ()
emitError e = modify $ \s -> s { errors = e : errors s }

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

getState :: (Eq k, Hashable k, Show k) => k -> (State -> HashMap k v) -> M v
getState k f = do
  m <- gets f
  case HashMap.lookup k m of
    Nothing -> error $ "getState: " ++ show k
    Just v  -> return v

lookupState :: (Eq k, Hashable k, Show k) => k -> (State -> HashMap k v) -> M (Maybe v)
lookupState k f = do
  m <- gets f
  return (HashMap.lookup k m)
