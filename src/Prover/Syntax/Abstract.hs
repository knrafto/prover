-- Syntax that has been scope-checked.
module Prover.Syntax.Abstract where

import Data.Text (Text)

import Prover.Syntax.Position

-- | A unique identifier for a thing with a name, used to determine if two names
-- refer to "the same thing", or two different things with the same name.
newtype NameId = NameId Int
  deriving (Eq, Show, Enum)

-- | An occurence of a name.
data Name = Name
  { -- | Unique identifier for the name. All names that refer to the same
    -- binding site have the same nameId.
    nameId          :: NameId
    -- | The spelling of this name.
  , nameText        :: Text
    -- | Where this name was used.
  , nameRange       :: Range
    -- | Where this name was defined.
  , nameBindingSite :: Range
  } deriving (Show)

data BindingType
  = VarBinding    -- ^ A local variable.
  | DefBinding    -- ^ A defined name.
  | AxiomBinding  -- ^ An assumed name.
  deriving (Show)

-- | Information about where a name was brought into scope.
data Binding = Binding
  { bindingNameId :: NameId
  , bindingSite   :: Range
  , bindingType   :: BindingType
  } deriving (Show)

instance HasRange Name where
  getRange = nameRange

data Expr
  = Var Name    -- ^ A bound variable.
  | Def Name    -- ^ A defined name.
  | Axiom Name  -- ^ An assumed name.
  | Hole Range  -- ^ An underscore hole.
  | Type Range
  | App Range Expr Expr
  | Pi Range Param Expr
  | Arrow Range Expr Expr
  | Lam Range Param Expr
  | Sigma Range Param Expr
  | Times Range Expr Expr
  | Pair Range Expr Expr
  | Equals Range Expr Expr
  deriving (Show)

type Param = (Name, Maybe Expr)

instance HasRange Expr where
  getRange = \case
    Var n         -> getRange n
    Def n         -> getRange n
    Axiom n       -> getRange n
    Hole r        -> r
    Type r        -> r
    App r _ _     -> r
    Pi r _ _      -> r
    Arrow r _ _   -> r
    Lam r _ _     -> r
    Sigma r _ _   -> r
    Times r _ _   -> r
    Pair r _ _    -> r
    Equals r _ _  -> r

data Decl
  = Define Name (Maybe Expr) Expr
  | Assume Name Expr
  deriving (Show)

newtype Module = Module [Decl]
  deriving (Show)
