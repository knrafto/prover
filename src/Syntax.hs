{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- Abstract syntax tree, in the style of Trees that grow:
-- https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf
module Syntax
    ( Id
    , Ann
    , Expr(..)
    , Param
    , Statement(..)
    , ann
    , HasNames(..)
    ) where

type family Id x
type family Ann x

data Expr x
    = Var   (Ann x) (Id x)
    | Type  (Ann x)
    | Hole  (Ann x)
    | App   (Ann x) (Expr x) (Expr x)
    | Tuple (Ann x) [Expr x]
    | Pi    (Ann x) (Param x) (Expr x)
    | Lam   (Ann x) (Param x) (Expr x)
    | Sigma (Ann x) (Param x) (Expr x)
    | Equal (Ann x) (Expr x) (Expr x)
    | Arrow (Ann x) (Expr x) (Expr x)
    | Times (Ann x) (Expr x) (Expr x)

deriving instance (Show (Id x), Show (Ann x)) => Show (Expr x)

type Param x = (Id x, Maybe (Expr x))

data Statement x
    = Define (Id x) (Maybe (Expr x)) (Expr x)
    | Assume (Id x) (Expr x)
    | Prove  (Id x) (Expr x)

deriving instance (Show (Id x), Show (Ann x)) => Show (Statement x)

ann :: Expr x -> Ann x
ann = \case
    Var   x _   -> x
    Type  x     -> x
    Hole  x     -> x
    App   x _ _ -> x
    Tuple x _   -> x
    Pi    x _ _ -> x
    Lam   x _ _ -> x
    Sigma x _ _ -> x
    Equal x _ _ -> x
    Arrow x _ _ -> x
    Times x _ _ -> x

class HasNames t where
    foldNames :: Monoid m => (Id x -> m) -> t x -> m

instance HasNames Expr where
    foldNames f = \case
        Var   _ i   -> f i
        Type  _     -> mempty
        Hole  _     -> mempty
        App   _ a b -> foldNames f a <> foldNames f b
        Tuple _ xs  -> foldMap (foldNames f) xs
        Pi    _ p e -> foldParam p <> foldNames f e
        Lam   _ p e -> foldParam p <> foldNames f e
        Sigma _ p e -> foldParam p <> foldNames f e
        Equal _ a b -> foldNames f a <> foldNames f b
        Arrow _ a b -> foldNames f a <> foldNames f b
        Times _ a b -> foldNames f a <> foldNames f b
      where
        foldParam (i, t) = f i <> foldMap (foldNames f) t

instance HasNames Statement where
    foldNames f = \case
        Define n ty body -> f n <> foldMap (foldNames f) ty <> foldNames f body
        Assume n ty      -> f n <> foldNames f ty
        Prove  n ty      -> f n <> foldNames f ty
