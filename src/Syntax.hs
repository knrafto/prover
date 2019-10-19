module Syntax where

import Data.Text (Text)

data Statement
    = Define Text (Maybe Expr) Expr
    | Assume Text Expr
    | Prove Expr
    deriving (Show)

data Expr
    = Hole
    | Var Text
    | Universe
    | Pi Text Expr Expr
    | Arrow Expr Expr
    | Lam Text Expr Expr
    | App Expr [Expr]
    | Sigma Text Expr Expr
    deriving (Show)