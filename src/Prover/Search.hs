module Prover.Search where

import Data.Function
import Data.List
import Data.Monoid

import Data.Heap qualified as Heap

import Prover.Monad

type Cost = Sum Int

-- | A search node representing the "unsolved goal state".
data Node = Node
  { nodeParent :: Maybe Node  -- ^ Parent node (Nothing if start node)
  , nodeDistance :: Cost  -- ^ Distance from start
  , nodeHeuristic :: Cost  -- ^ Heuristic distance to the goal
  , nodeProblem :: UnificationProblem
  }

nodeCost :: Node -> Cost
nodeCost node = nodeDistance node + nodeHeuristic node

instance Eq Node where
  (==) = (==) `on` nodeCost

instance Ord Node where
  compare = compare `on` nodeCost

-- | Decides whether a node is a solution.
isSolved :: Node -> Bool
isSolved = error "isSolved" -- TODO

-- | Enumerate the children of a node, along 
children :: Node -> M [Node]
children = error "children" -- TODO

-- | Run A* search.
-- TODO: need history of explored nodes. must be able to reconstruct tree at each step
-- use node ids?
search :: Cost -> Node -> M ()
search maxDistance initialNode = go (Heap.singleton initialNode)
  where
    go heap = case Heap.viewMin heap of
      Nothing -> error "exhausted search space" -- TODO
      Just (node, heap)
        | isSolved node -> error "found a solution" -- TODO
        | nodeDistance node > maxDistance -> error "gave up search" -- TODO
        | otherwise -> do
          ns <- children node
          go (foldl' (flip Heap.insert) heap ns)
