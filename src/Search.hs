{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Search where

import Control.Applicative
import Control.Monad
import Data.Foldable

import Control.Monad.State.Class

-- A semi-decidable search result. The result is either non-empty (with a list
-- of possibilities), empty (with a reason), or unknown (meaning we've given up).
data Result e a
    = Ok [a]
    | Fail e
    | Unknown

instance Functor (Result e) where
    fmap f (Ok xs) = Ok (map f xs)
    fmap _ (Fail e) = Fail e
    fmap _ Unknown = Unknown

instance Monoid e => Applicative (Result e) where
    pure = return
    (<*>) = ap

instance Monoid e => Monad (Result e) where
    return a = Ok [a]

    Ok as >>= k = asum (fmap k as)
    Fail e >>= _ = Fail e
    Unknown >>= _ = Unknown

instance Monoid e => Alternative (Result e) where
    empty = Fail mempty

    Ok as <|> Ok bs = Ok (as ++ bs)
    Ok as <|> _ = Ok as
    _ <|> Ok bs = Ok bs
    Unknown <|> _ = Unknown
    _ <|> Unknown = Unknown
    Fail s <|> Fail t = Fail (s <> t)

instance Monoid e => MonadPlus (Result e) where

type Search s e a = Int -> s -> Result e a

-- Search monad, with state and errors.
-- Use `deepen` to make a subtree for iterative deepending.
-- Inspired by "Reinventing Haskell backtracking": https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/atps09.pdf
newtype SearchM s e a = SearchM { runSearchM :: forall b. (a -> Search s e b) -> Search s e b }

instance Functor (SearchM s e) where
    fmap f (SearchM m) = SearchM (\k -> m (\x -> k (f x)))

instance Applicative (SearchM s e) where
    pure x = SearchM (\k -> k x)
    SearchM f <*> SearchM g = SearchM (\bfr -> f (\ab -> g (\x -> bfr (ab x))))

instance Monad (SearchM s e) where
    return = pure
    m >>= k = SearchM (\c -> runSearchM m (\a -> runSearchM (k a) c))

instance Monoid e => Alternative (SearchM s e) where
    empty = SearchM (\_ _ _ -> empty)
    SearchM m <|> SearchM n = SearchM (\k d s -> m k d s <|> n k d s)

instance Monoid e => MonadPlus (SearchM s e) where

instance MonadState s (SearchM s e) where
    get = SearchM (\k d s -> k s d s)
    put s = SearchM (\k d _ -> k () d s)

throw :: e -> SearchM s e a
throw e = SearchM (\_ _ _ -> Fail e)

deepen :: SearchM s e a -> SearchM s e a
deepen (SearchM m) = SearchM (\k d s -> if d == 0 then Unknown else m k (d - 1) s)

runSearch :: Monoid e => Int -> SearchM s e a -> s -> Result e a
runSearch limit m s = go 0
  where
    go n | n >= limit = Unknown
         | otherwise = case runSearchM m (\a _ _ -> return a) n s of
            Unknown -> go (n + 1)
            r -> r
