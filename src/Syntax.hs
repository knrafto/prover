module Syntax where

import Data.Text (Text)

data Statement
    = Define Text Expr
    | Assume Text Expr
    | Prove Expr
    deriving (Show)

data Expr
    = Var Text
    | Universe
    | Pi Text Expr Expr
    | Arrow Expr Expr
    | Lam Text Expr Expr
    | App Expr [Expr]
    | Sigma Text Expr Expr
    deriving (Show)