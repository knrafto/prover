module Syntax where

import           Location

-- Expressions are labeled with a value of type l, and variables have type v.
data Expr l v
    = Hole l
    | Var l v
    | Type l
    | Equal l (Expr l v) (Expr l v)
    | Pi l [Param l v] (Expr l v)
    | Arrow l (Expr l v) (Expr l v)
    | Lam l [Param l v] (Expr l v)
    | App l (Expr l v) [Expr l v]
    | Sigma l [Param l v] (Expr l v)
    | Times l (Expr l v) (Expr l v)
    | Tuple l [Expr l v]
    deriving (Show)

type Param l v = (Ident, Expr l v)

ann :: Expr l v -> l
ann e = case e of
    Hole l      -> l
    Var l _     -> l
    Type l      -> l
    Equal l _ _ -> l
    Pi    l _ _ -> l
    Arrow l _ _ -> l
    Lam   l _ _ -> l
    App   l _ _ -> l
    Sigma l _ _ -> l
    Times l _ _ -> l
    Tuple l _   -> l

data Statement l v
    = Define Ident [Param l v] (Maybe (Expr l v)) (Expr l v)
    | Assume Ident (Expr l v)
    | Prove Ident (Expr l v)
    deriving (Show)
