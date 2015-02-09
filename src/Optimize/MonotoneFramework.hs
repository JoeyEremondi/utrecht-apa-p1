--Joseph Eremondi UU# 4229924
--Utrecht University, APA 2015
--Project one: dataflow analysis

module MonotoneFramework where

import qualified Data.Set as Set

--Wrapper for a control flow graph
newtype CFG block = CFG (Set.Set (block, block))

incoming :: (Ord block) => CFG block -> block -> Set.Set block
incoming (CFG controlFlow) l = Set.map snd $ Set.filter ((== l) . fst) controlFlow

class (Ord a) => CompleteLattice a where
  latticeTop :: a
  latticeBottom :: a
  latticeJoin :: a -> a -> a
  (|^|) :: a -> a -> a --infix notation for join
  iota :: a --Extremal value for our analysis

joinAll :: (CompleteLattice a) => Set.Set a -> a
joinAll = Set.foldr latticeJoin latticeBottom

class (Ord block) => MonotoneFramework block where
    --We either reverse all labels, or don't reverse them
    makePairs :: CFG block -> CFG block
    extremalBlocks :: Set.Set block

--TODO this is infinite recursion!!!
analysis :: (CompleteLattice lat, MonotoneFramework block) => CFG block -> block -> lat
analysis controlFlow label = helper labelPairs
  if Set.member label extremalBlocks
  then iota
  else joinAll incomingBlocks
  where
    recFun = analysis controlFlow
    labelPairs = makePairs controlFlow --TODO avoid recomputing at each stage?
    incomingBlocks = Set.map recFun $ incoming labelPairs label
