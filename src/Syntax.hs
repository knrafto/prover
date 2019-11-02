module Syntax where

import Data.Text (Text)

data Statement
    = Define Text (Maybe Expr) Expr
    | Assume Text Expr
    | Prove Text Expr
    deriving (Show)

data Expr
    = Hole
    | Var Text
    | Universe
    | Equal Expr Expr
    | Pi Text Expr Expr
    | Arrow Expr Expr
    | Lam Text Expr Expr
    | App Expr [Expr]
    | Sigma Text Expr Expr
    | Times Expr Expr
    | Tuple [Expr]
    deriving (Show)