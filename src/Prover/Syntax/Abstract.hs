-- Syntax that has been scope-checked.
module Prover.Syntax.Abstract where

import Prover.Syntax.Position

-- TODO: text, range, binding site, unique id?
data Name = Name
  { nameRange :: Range
  } deriving (Show)

instance HasRange Name where
  getRange = nameRange

data Decls
  = Define Name (Maybe Expr) Expr
  | Assume Name Expr
  | Prove  Name Expr
  deriving (Show)

data Expr
  = Var Name  -- ^ A bound variable.
  | Def Name  -- ^ A defined or assumed name.
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
