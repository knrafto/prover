{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Search where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Monoid

import Control.Monad.State.Class

-- A semi-decidable search result. The result is either non-empty (with a list
-- of possibilities), empty (with a reason), or unknown (meaning we've given up).
data Result a
    = Ok [a]
    | Fail (First String) 
    | Unknown

instance Functor Result where
    fmap f (Ok xs) = Ok (map f xs)
    fmap _ (Fail e) = Fail e
    fmap _ Unknown = Unknown

instance Applicative Result where
    pure = return
    (<*>) = ap

instance Monad Result where
    return a = Ok [a]

    Ok as >>= k = asum (fmap k as)
    Fail e >>= _ = Fail e
    Unknown >>= _ = Unknown

instance Alternative Result where
    empty = Fail mempty

    Ok as <|> Ok bs = Ok (as ++ bs)
    Ok as <|> _ = Ok as
    _ <|> Ok bs = Ok bs
    Unknown <|> _ = Unknown
    _ <|> Unknown = Unknown
    Fail s <|> Fail t = Fail (s <> t)

instance MonadPlus Result where

type Search s a = Int -> s -> Result a

-- Search monad, with state and errors.
-- Use `deepen` to make a subtree for iterative deepending.
-- Inspired by "Reinventing Haskell backtracking": https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/atps09.pdf
newtype SearchM s a = SearchM { runSearchM :: forall b. (a -> Search s b) -> Search s b }

instance Functor (SearchM s) where
    fmap f (SearchM m) = SearchM (\k -> m (\x -> k (f x)))

instance Applicative (SearchM s) where
    pure x = SearchM (\k -> k x)
    SearchM f <*> SearchM g = SearchM (\bfr -> f (\ab -> g (\x -> bfr (ab x))))

instance Monad (SearchM s) where
    return = pure
    m >>= k = SearchM (\c -> runSearchM m (\a -> runSearchM (k a) c))

instance Alternative (SearchM s) where
    empty = SearchM (\_ _ _ -> empty)
    SearchM m <|> SearchM n = SearchM (\k d s -> m k d s <|> n k d s)

instance MonadPlus (SearchM s) where

instance MonadState s (SearchM s) where
    get = SearchM (\k d s -> k s d s)
    put s = SearchM (\k d _ -> k () d s)

throw :: String -> SearchM s a
throw e = SearchM (\_ _ _ -> Fail (First (Just e)))

trace :: String -> SearchM s a -> SearchM s a
trace _ p = p

deepen :: String -> SearchM s a -> SearchM s a
deepen _ (SearchM m) = SearchM (\k d s -> if d == 0 then Unknown else m k (d - 1) s)

runSearch :: Int -> SearchM s a -> s -> Result a
runSearch limit m s = go 0
  where
    go n | n >= limit = Unknown
         | otherwise = case runSearchM m (\a _ _ -> return a) n s of
            Unknown -> go (n + 1)
            r -> r
