{-# LANGUAGE RecordWildCards #-}
--Joseph Eremondi UU# 4229924
--Utrecht University, APA 2015
--Project one: dataflow analysis

module Optimize.MonotoneFramework where

import qualified Data.Set as Set
--import Data.Ix
--import Data.Array.ST
--import Control.Monad
--import Control.Monad.ST
import qualified Data.Map as Map
--import qualified Data.Array as Array

--Wrapper for a control flow graph
newtype CFG block = CFG (Set.Set (block, block))

newtype FlowEdge label = FlowEdge (label, label)

data AnalysisDirection = ForwardAnalysis | BackwardAnalysis

data ProgramInfo label = ProgramInfo {
  edgeMap :: label -> [label],
  --labelRange :: (label, label),
  allLabels :: [label],
  labelPairs :: [(label, label)],
  isExtremal :: label -> Bool
  
  }

getFlowEdge :: AnalysisDirection -> (label,label) -> FlowEdge label
getFlowEdge ForwardAnalysis e = FlowEdge e
getFlowEdge BackwardAnalysis (l1, l2) = FlowEdge (l2, l1)


incoming :: (Ord block) => CFG block -> block -> Set.Set block
incoming (CFG controlFlow) l = Set.map snd $ Set.filter ((== l) . fst) controlFlow

data Lattice a = Lattice {
  --latticeTop :: a
  latticeBottom :: a,
  latticeJoin :: a -> a -> a,
  iota :: a, --Extremal value for our analysis
  lleq :: a -> a -> Bool,
  flowDirection :: AnalysisDirection
  }


joinAll :: (Lattice a) -> [a] -> a
joinAll Lattice{..} = foldr latticeJoin latticeBottom

--worklist algo for least fixed point
--We don't actually need to pass in bottom, but it helps the typechecker
--figure out which lattice we're using
minFP :: (Ord label) =>
         Lattice payload 
         -> (Map.Map label payload -> label -> payload -> payload)
         -> ProgramInfo label
         -> (Map.Map label payload, Map.Map label payload) 
minFP lat@(Lattice{..}) f info = (mfpOpen, error "TODO closed in edge-framework?" {-mfpClosed-})
  where
    mfpClosed = Map.mapWithKey (f mfpOpen) mfpOpen
    --stResult :: ST s [(label, payload)]
    initialSolns = foldr (\l solnsSoFar ->
                             if isExtremal info l
                             then Map.insert l latticeBottom solnsSoFar
                             else Map.insert l iota solnsSoFar
                           ) Map.empty (allLabels info)
    mfpOpen = iterateSolns initialSolns (labelPairs info)
    iterateSolns currentSolns [] = currentSolns
    iterateSolns currentSolns (cfgEdge:rest) = let
      flowEdge = getFlowEdge flowDirection cfgEdge
      (FlowEdge (l,l')) = flowEdge 
      al = currentSolns Map.! l
      al' = currentSolns Map.! l'
      fal = f currentSolns l al
      (newPairs, newSolns) =
        if (fal `lleq` al') 
        then let
            theMap = Map.insert l' (latticeJoin al' fal) currentSolns
            thePairs = map (\lNeighbour -> (l', lNeighbour) ) $ edgeMap info l'
          in (thePairs, theMap)
        else ([], currentSolns)
      in iterateSolns newSolns (newPairs ++ rest)
        
      
      
    
          



