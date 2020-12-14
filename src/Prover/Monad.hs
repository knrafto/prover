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
import Prover.Position
import Prover.Syntax
import Prover.Term

-- | A unique identifier for type-checking equations.
newtype EquationId = EquationId Int
  deriving (Eq, Ord, Show, Enum, Hashable)

-- TODO: move somewhere else?
-- TODO: should all error names end in Error?
data Error
  -- | A name could not be resolved.
  = UnboundNameError Range Text
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
  | LateImplicitParam Range Name
  -- | Infix operators could not be parsed.
  | InfixParseError Range
  deriving (Show)

-- | Constraints for unification.
data Constraint
  = Solved  -- ^ Constraint is true
  | Inconsistent  -- ^ Constraint is false
  | TermEq Ctx Type Term Term
  | SpineEq Ctx Type [(Term, Term)]
  | And [Constraint]
  | ExactlyOne [Constraint]
  | Guarded Constraint Constraint
  deriving (Show)

-- | A unification problem is a set of metavariables (which stand for unknown
-- terms) and a set of constraints involving those metavariables. A solution to
-- a unification problem is an assignment of metavariables to terms (a
-- metavariable substitution) that satisfies the constraints. A unification
-- problem can have zero, one, or many solutions.
--
-- Unification is used in the implementation of both type-checking and proof
-- search. For type-checking, the goal is to find a unique solution to a
-- unification problem, and for proof search, the goal is to find any solution.
--
-- Any "bookkeeping" information for error message (source range, for example)
-- is tracked separately by the type-checker. TODO: move to Unify.hs
data UnificationProblem = UnificationProblem
  { -- | The metavariables in the unification problem.
    problemMetas :: HashSet MetaId
    -- | A (partial) substitution of metavariables to terms.
  , problemMetaTerms :: HashMap MetaId Term
    -- | Unification constraints.
  , problemConstraints :: HashMap EquationId Constraint
  } deriving (Show)

-- | Get the unsolved metas in a unification problem.
problemUnsolvedMetas :: UnificationProblem -> HashSet MetaId
problemUnsolvedMetas problem = HashSet.difference
  (problemMetas problem)
  (HashMap.keysSet (problemMetaTerms problem))

-- | The empty unification problem.
emptyProblem :: UnificationProblem
emptyProblem = UnificationProblem
  { problemMetas       = HashSet.empty
  , problemMetaTerms   = HashMap.empty
  , problemConstraints = HashMap.empty
  }

-- | Add a metavariable to a unification problem.
addProblemMeta :: MetaId -> UnificationProblem -> UnificationProblem
addProblemMeta id problem =
  problem { problemMetas  = HashSet.insert id (problemMetas problem) }

-- | Add a constraint to a unification problem.
addProblemConstraint :: EquationId -> Constraint -> UnificationProblem -> UnificationProblem
addProblemConstraint id c problem =
  problem { problemConstraints = HashMap.insert id c (problemConstraints problem) }

-- | Global type-checking state.
data State = State
  { -- | Error messages.
    errors              :: [Error]
    -- | Generating fresh things.
  , nextNameId          :: !NameId
  , nextMetaId          :: !MetaId
  , nextEquationId      :: !EquationId
    -- | Fixity declarations.
  , fixities            :: HashMap Text (Fixity, Int)
    -- | Globally-defined names.
  , globalNames         :: HashMap Text NameId
    -- | Definitions. TODO: use a record?
  , defNames            :: HashMap NameId Name
  , defImplicits        :: HashMap NameId Int
  , defTypes            :: HashMap NameId Type
  , defTerms            :: HashMap NameId Term
    -- | Axioms. TODO: use a record?
  , axiomNames          :: HashMap NameId Name
  , axiomImplicits      :: HashMap NameId Int
  , axiomTypes          :: HashMap NameId Type
  , axiomRules          :: HashMap NameId [Rule]
    -- | Global metavariable substitution. When we add a new global definition
    -- (axiom, etc.) after type-checking, we also stick the meta substitution
    -- here and substitute "lazily" instead of substituting everywhere all at
    -- once. Any unsolved metas after type-checking will be here as well, but
    -- they will not have a term, so they effectively become constants.
  , metaCtxs            :: HashMap MetaId Ctx
  , metaTypes           :: HashMap MetaId Type
  , metaTerms           :: HashMap MetaId Term
    -- | Type-checking information.
  , metaRanges          :: HashMap MetaId Range
  , equationRanges      :: HashMap EquationId Range
  , goalKinds           :: HashMap MetaId GoalKind
  , unificationProblem  :: UnificationProblem
  } deriving (Show)

initialState :: State
initialState = State
  { errors              = []
  , nextNameId          = NameId 0
  , nextMetaId          = MetaId 0
  , nextEquationId      = EquationId 0
  , fixities            = HashMap.empty
  , globalNames         = HashMap.empty
  , defNames            = HashMap.empty
  , defImplicits        = HashMap.empty
  , defTypes            = HashMap.empty
  , defTerms            = HashMap.empty
  , axiomNames          = HashMap.empty
  , axiomImplicits      = HashMap.empty
  , axiomTypes          = HashMap.empty
  , axiomRules          = HashMap.empty
  , metaRanges          = HashMap.empty
  , metaCtxs            = HashMap.empty
  , metaTypes           = HashMap.empty
  , metaTerms           = HashMap.empty
  , equationRanges      = HashMap.empty
  , goalKinds           = HashMap.empty
  , unificationProblem  = emptyProblem
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

freshEquationId :: M EquationId
freshEquationId = do
  s <- get
  let id = nextEquationId s
  put s { nextEquationId = succ id }
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
