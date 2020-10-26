module Prover.Search where

import Data.Function
import Data.List
import Data.Monoid

import Data.Heap (Heap)
import Data.Heap qualified as Heap

type Cost = Sum Int

-- | A search node representing the "unsolved goal state".
data Node = Node
  { parent :: Maybe Node  -- ^ Parent node (Nothing if start node)
  , distance :: Cost  -- ^ Distance from start
  , heuristic :: Cost  -- ^ Heuristic distance to the goal
    -- TODO: unification problem
  }

estimatedCost :: Node -> Cost
estimatedCost node = distance node + heuristic node

instance Eq Node where
  (==) = (==) `on` estimatedCost

instance Ord Node where
  compare = compare `on` estimatedCost

-- | Decides whether a node is a solution.
isSolved :: Node -> Bool
isSolved = error "isSolved" -- TODO

-- | Enumerate the children of a node, along 
children :: Monad m => Node -> m [Node]
children = error "children" -- TODO

-- | Run A* search.
-- TODO: need history of explored nodes. must be able to reconstruct tree at each step
-- use node ids?
search :: Monad m => Cost -> Heap Node -> m ()
search maxCost heap = case Heap.viewMin heap of
  Nothing -> error "exhausted search space" -- TODO
  Just (node, heap)
    | isSolved node -> error "found a solution" -- TODO
    | estimatedCost node > maxCost -> error "gave up search" -- TODO
    | otherwise -> do
      ns <- children node
      search maxCost (foldl' (flip Heap.insert) heap ns)
