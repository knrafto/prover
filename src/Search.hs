{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Search where

import Control.Applicative
import Control.Monad
import Data.Tree

import Control.Monad.State

-- The list monad, with a tree trace.
data Result a = Result [a] (Forest String)

instance Functor Result where
    fmap f (Result xs bs) = Result (map f xs) bs

instance Applicative Result where
    pure = return
    (<*>) = ap

instance Monad Result where
    return a = Result [a] []

    Result xs bs >>= k =
        let (ys, bs') = foldr go ([], []) (map k xs) in Result ys (bs ++ bs')
      where
        go (Result as f) (as', f') = (as ++ as', f ++ f') 

instance Alternative Result where
    empty = Result [] []
    Result xs bs <|> Result ys cs = Result (xs ++ ys) (bs ++ cs)

instance MonadPlus Result where

newtype SearchM s a = SearchM { runSearchM :: StateT s Result a }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus, MonadState s)

throw :: String -> SearchM s a
throw e = SearchM (lift (Result [] [Node e []]))

trace :: String -> SearchM s a -> SearchM s a
trace e m = SearchM (StateT (\s ->
    let Result as bs = runStateT (runSearchM m) s in Result as [Node e bs]))

runSearch :: SearchM s a -> s -> Result (a, s)
runSearch m s = runStateT (runSearchM m) s
