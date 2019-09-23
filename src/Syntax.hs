module Syntax where

import Data.Text (Text)

data Statement
    = Define Text Params Expr Expr
    | Assume Text Expr
    deriving (Show)

type Params = [(Text, Expr)]

data Expr
    = Var Text
    | Apply Expr [Expr]
    | Sigma Params Expr
    | Pi Params Expr
    | Lambda Params Expr
    | Arrow Expr Expr
    deriving (Show)