module Syntax where

import Data.Text (Text)

-- A range of text in the source file, represented by two offsets.
data SrcSpan = SrcSpan !Int !Int
    deriving (Eq, Show)

data Located e = L SrcSpan e

instance Show e => Show (Located e) where
    showsPrec d (L _ e) = showsPrec d e

unLoc :: Located e -> e
unLoc (L _ e) = e

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