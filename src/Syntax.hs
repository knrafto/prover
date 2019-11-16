module Syntax where

import           Location

import           Data.Text                      ( Text )

type Param = (Text, LExpr)

data Expr
    = Hole
    | Var Text
    | Universe
    | Equal LExpr LExpr
    | Pi [Param] LExpr
    | Arrow LExpr LExpr
    | Lam [Param] LExpr
    | App LExpr [LExpr]
    | Sigma [Param] LExpr
    | Times LExpr LExpr
    | Tuple [LExpr]
    deriving (Show)
type LExpr = Located Expr

data Statement
    = Define Text [Param] (Maybe LExpr) LExpr
    | Assume Text LExpr
    | Prove Text LExpr
    deriving (Show)
type LStatement = Located Statement
