{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax where

-- AST in the style of Trees that grow:
-- https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf
type family Id x
type family Ann x

data Expr x
    = Var (Ann x) (Id x)
    | Type (Ann x)
    | Hole (Ann x)
    | App (Ann x) (Expr x) (Expr x)
    | Tuple (Ann x) [Expr x]
    | Pi (Ann x) [Param x] (Expr x)
    | Lambda (Ann x) [Param x] (Expr x)
    | Sigma (Ann x) [Param x] (Expr x)
    | Equal (Ann x) (Expr x) (Expr x)
    | Arrow (Ann x) (Expr x) (Expr x)
    | Times (Ann x) (Expr x) (Expr x)

deriving instance (Show (Id x), Show (Ann x)) => Show (Expr x)

type Param x = (Id x, Expr x)

data Statement x
    = Define (Id x) (Maybe (Expr x)) (Expr x)
    | Assume (Id x) (Expr x)
    | Prove (Id x) (Expr x)

deriving instance (Show (Id x), Show (Ann x)) => Show (Statement x)

ann :: Expr x -> Ann x
ann = \case
    Var x _      -> x
    Type x       -> x
    Hole x       -> x
    App x _ _    -> x
    Tuple x _    -> x
    Pi     x _ _ -> x
    Lambda x _ _ -> x
    Sigma  x _ _ -> x
    Equal  x _ _ -> x
    Arrow  x _ _ -> x
    Times  x _ _ -> x
