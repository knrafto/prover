module Syntax where

import Data.Text (Text)

type Param = (Text, Expr)

data Expr
    = Hole
    | Var Text
    | Universe
    | Equal Expr Expr
    | Pi [Param] Expr
    | Arrow Expr Expr
    | Lam [Param] Expr
    | App Expr [Expr]
    | Sigma [Param] Expr
    | Times Expr Expr
    | Tuple [Expr]
    deriving (Show)

data Statement
    = Define Text [Param] (Maybe Expr) Expr
    | Assume Text Expr
    | Prove Text Expr
    deriving (Show)