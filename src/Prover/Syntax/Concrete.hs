-- | The result of parsing.
module Prover.Syntax.Concrete where

import Data.Text (Text)

import Prover.Syntax.Position

data Name = Name
  { nameRange :: Range
  , nameText :: Text
  } deriving (Show)

instance HasRange Name where
  getRange = nameRange

data Expr
  = Id      Name
  | Hole    Range
  | Type    Range
  | Pi      Range Param Expr
  | Lam     Range Param Expr
  | Sigma   Range Param Expr
  | App     Range Expr Expr
  | Arrow   Range Expr Expr
  | Times   Range Expr Expr
  | Pair    Range Expr Expr
  | Equals  Range Expr Expr
  deriving (Show)

instance HasRange Expr where
  getRange = \case
    Id      n     -> getRange n
    Hole    r     -> r
    Type    r     -> r
    Pi      r _ _ -> r
    Lam     r _ _ -> r
    Sigma   r _ _ -> r
    App     r _ _ -> r
    Arrow   r _ _ -> r
    Times   r _ _ -> r
    Equals  r _ _ -> r
    Pair    r _ _ -> r

data Param = Param
  { paramName         :: Name
  , paramAnnotation   :: Maybe Expr
  } deriving (Show)

instance HasRange Param where
  -- TODO: store full range including annotation (and parens)?
  getRange = getRange . paramName

data Decl
  = Define Name [Param] [Param] (Maybe Expr) Expr
  | Assume Name [Param] [Param] Expr
  | Rewrite Name [Param] Expr Expr
  deriving (Show)

newtype Module = Module [Decl]
  deriving (Show)
