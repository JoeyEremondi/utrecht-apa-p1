--Joseph Eremondi UU# 4229924
--Utrecht University, APA 2015
--Project one: dataflow analysis

module Optimize.MonotoneFramework where

import qualified Data.Set as Set
import Data.Ix
import Data.Array.ST
import Control.Monad
import Control.Monad.ST
import qualified Data.Map as Map
import qualified Data.Array as Array

--Wrapper for a control flow graph
newtype CFG block = CFG (Set.Set (block, block))

data ProgramInfo label = ProgramInfo {
  edgeMap :: label -> [label],
  labelRange :: (label, label),
  allLabels :: [label],
  labelPairs :: [(label, label)],
  isExtremal :: label -> Bool
  
  }

incoming :: (Ord block) => CFG block -> block -> Set.Set block
incoming (CFG controlFlow) l = Set.map snd $ Set.filter ((== l) . fst) controlFlow

class (Ord a, Eq a) => Lattice a where
  --latticeTop :: a
  latticeBottom :: a
  latticeJoin :: a -> a -> a
  iota :: a --Extremal value for our analysis
  lleq :: a -> a -> Bool



joinAll :: (Lattice a) => Set.Set a -> a
joinAll = Set.foldr latticeJoin latticeBottom

--worklist algo for least fixed point
minFP :: (Lattice payload, Ord label) =>
         (payload -> payload)
         -> ProgramInfo label
         -> (Map.Map label payload, Map.Map label payload) 
minFP f info = (mfpOpen, mfpClosed)
  where
    mfpClosed = Map.map f mfpOpen
    --stResult :: ST s [(label, payload)]
    initialSolns = foldr (\l solnsSoFar ->
                             if isExtremal info l
                             then Map.insert l latticeBottom solnsSoFar
                             else Map.insert l iota solnsSoFar
                           ) Map.empty (allLabels info)
    mfpOpen = iterateSolns initialSolns (labelPairs info)
    iterateSolns currentSolns [] = currentSolns
    iterateSolns currentSolns ((l,l'):rest) = let
      al = currentSolns Map.! l
      al' = currentSolns Map.! l'
      fal = f al
      (newPairs, newSolns) =
        if (fal `lleq` al') 
        then let
            theMap = Map.empty --Map.insert l' (join al' fal) currentSolns
            thePairs = map (\lNeighbour -> (l', lNeighbour) ) $ edgeMap info l'
          in (thePairs, theMap)
        else ([], currentSolns)
      in iterateSolns newSolns (newPairs ++ rest)
        
      
      
    
          



