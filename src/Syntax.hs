module Syntax where

import           Location

type Param = (Ident, Expr)

type Expr = Located Expr'

data Expr'
    = Hole
    | Ident Ident
    | Type
    | Equal Expr Expr
    | PiExpr [Param] Expr
    | Arrow Expr Expr
    | LamExpr [Param] Expr
    | AppExpr Expr [Expr]
    | SigmaExpr [Param] Expr
    | Times Expr Expr
    | Tuple [Expr]
    deriving (Show)

type Statement = Located Statement'

data Statement'
    = Define Ident [Param] (Maybe Expr) Expr
    | Assume Ident Expr
    | Prove Ident Expr
    deriving (Show)
