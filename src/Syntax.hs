module Syntax where

import Data.Text (Text)

data Statement
    = Define Text Params Expr Expr
    | Assume Text Expr
    | Prove Expr
    deriving (Show)

type Params = [(Text, Expr)]

data Expr
    = Var Text
    | Universe
    | Pi Params Expr
    | Arrow Expr Expr
    | Lam Params Expr
    | App Expr [Expr]
    | Sigma Params Expr
    deriving (Show)