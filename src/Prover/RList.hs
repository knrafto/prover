module Prover.RList where

import Prelude hiding ((!!))

-- | A strict list where new things go on the right.
data RList a
  = Empty
  | !(RList a) :> !a
  deriving (Eq, Show, Functor, Foldable, Traversable)

infixl 9 !!

(!!) :: RList a -> Int -> a
Empty !! _    = error "RList.!!"
(_ :> a) !! 0 = a
(l :> _) !! i = l !! (i - 1)

elemIndices :: Eq a => a -> RList a -> [Int]
elemIndices a = go 0
  where
  go _ Empty = []
  go !i (xs :> x)
    | a == x    = i : go (i + 1) xs
    | otherwise = go (i + 1) xs
