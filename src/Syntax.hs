module Syntax where

import           Location

import           Data.Text                      ( Text )

type Param = (Text, LExpr)

data Expr
    = Hole
    | Ident Text
    | Type
    | Equal LExpr LExpr
    | PiExpr [Param] LExpr
    | Arrow LExpr LExpr
    | LamExpr [Param] LExpr
    | AppExpr LExpr [LExpr]
    | SigmaExpr [Param] LExpr
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
