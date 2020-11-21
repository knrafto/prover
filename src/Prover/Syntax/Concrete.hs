-- | The result of parsing.
module Prover.Syntax.Concrete where

import Data.Text (Text)

import Prover.Position

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
  | Pi      Range [ParamGroup] Expr
  | Lam     Range [ParamGroup] Expr
  | Sigma   Range [ParamGroup] Expr
  | Apps    Range [Expr]
  | Arrow   Range Expr Expr
  | Pair    Range Expr Expr
  deriving (Show)

instance HasRange Expr where
  getRange = \case
    Id      n     -> getRange n
    Hole    r     -> r
    Type    r     -> r
    Pi      r _ _ -> r
    Lam     r _ _ -> r
    Sigma   r _ _ -> r
    Apps    r _   -> r
    Arrow   r _ _ -> r
    Pair    r _ _ -> r

data ParamGroup = ParamGroup [Name] (Maybe Expr)
  deriving (Show)

data Decl
  = Define Name [ParamGroup] [ParamGroup] (Maybe Expr) Expr
  | Assume Name [ParamGroup] [ParamGroup] Expr
  | Rewrite Name [ParamGroup] Expr Expr
  | Fixity Fixity Int Text
  deriving (Show)

newtype Module = Module [Decl]
  deriving (Show)
