{-Joseph Eremondi UU# 4229924
  Utrecht University, APA 2015
  Project one: dataflow analysis
  March 17, 2015 -}

{-# LANGUAGE RecordWildCards #-}

{-|
General framework for constructing lattices and finding fixpoints
of monotone functions.
|-}
module Optimize.MonotoneFramework (
  AnalysisDirection(..),
  ProgramInfo(..),
  Lattice(..),
  joinAll,
  minFP,
  printGraph
  )where

import qualified Data.HashMap.Strict               as Map

import qualified Data.Graph.Inductive.Graph        as Graph
import qualified Data.Graph.Inductive.PatriciaTree as Gr

import qualified Data.GraphViz                     as Viz
import qualified Data.GraphViz.Attributes.Complete as VA
import           Data.GraphViz.Printing            (renderDot)
import           Data.List                         (foldl')

import           Data.Hashable

import           Data.Text.Lazy                    (pack, unpack)



newtype FlowEdge label = FlowEdge (label, label)

data AnalysisDirection = ForwardAnalysis | BackwardAnalysis

data ProgramInfo label = ProgramInfo {
  edgeMap    :: label -> [label],
  --labelRange :: (label, label),
  allLabels  :: [label],
  labelPairs :: [(label, label)],
  isExtremal :: label -> Bool

  }

{-|
Useful for debugging. Prints the graphviz string to render
a representation of a control-flow graph
|-}
printGraph
  :: (Ord label)
  => (label -> Int)
  -> (label -> String)
  -> ProgramInfo label
  -> String
printGraph intMap strMap pInfo =
  let
    nodes = map (\n -> (intMap n, strMap n)) $ allLabels pInfo
    grWithNodes = (Graph.insNodes nodes Graph.empty) :: (Gr.Gr String ())
    edges = map (\(n1, n2) -> (intMap n1, intMap n2, () ) ) (labelPairs pInfo)
    theGraph = (Graph.insEdges edges grWithNodes) :: (Gr.Gr String () )
    defaultParams = Viz.defaultParams :: (Viz.GraphvizParams Graph.Node String () () String )
    ourParams = defaultParams {Viz.fmtNode = \(_,s) -> [VA.Label $ VA.StrLabel $ pack s]}
  in unpack $ renderDot $ Viz.toDot $ Viz.graphToDot ourParams theGraph

{-|
Either reverse and edge, or don't, depending on whether we are doing
forwards or backwards analysis
|-}
getFlowEdge :: AnalysisDirection -> (label,label) -> FlowEdge label
getFlowEdge ForwardAnalysis e = FlowEdge e
getFlowEdge BackwardAnalysis (l1, l2) = FlowEdge (l2, l1)

{-|
Abstract type representing a lattice and the operations that can
be performed on it.
|-}
data Lattice a = Lattice {
  --latticeTop :: a
  latticeBottom :: a,
  latticeJoin   :: a -> a -> a,
  iota          :: a, --Extremal value for our analysis
  lleq          :: a -> a -> Bool,
  flowDirection :: AnalysisDirection
  }

{-|
Iteratively join all the lattice elements in a list
|-}
joinAll :: (Lattice a) -> [a] -> a
joinAll Lattice{..} = foldl' latticeJoin latticeBottom

{-|
Given a Lattice,
a transfer which takes current stored values, a block label, and a payload
and produces a new payload,
and the flow information for our program,
generate the dictionaries representing the open and closed fix-points
of the given transfer function.
|-}
minFP :: (Hashable label, Eq label, Show label, Show payload) =>
         Lattice payload
         -> (Map.HashMap label payload -> label -> payload -> payload)
         -> ProgramInfo label
         -> (Map.HashMap label payload, Map.HashMap label payload)
minFP lat@(Lattice{..}) f info = (mfpOpen, mfpClosed)
  where
    mfpClosed = Map.mapWithKey (f mfpOpen) mfpOpen
    --stResult :: ST s [(label, payload)]
    initialSolns = foldr (\l solnsSoFar ->
                             if isExtremal info l
                             then Map.insert l iota solnsSoFar
                             else Map.insert l latticeBottom solnsSoFar
                           ) Map.empty (allLabels info)
    mfpOpen =  iterateSolns initialSolns (labelPairs info)
    iterateSolns currentSolns [] = currentSolns
    iterateSolns currentSolns (cfgEdge:rest) =  let
      flowEdge = getFlowEdge flowDirection cfgEdge
      (FlowEdge (l,l')) = flowEdge
      al = currentSolns Map.! l
      al' = currentSolns Map.! l'
      fal = f currentSolns l al
      (newPairs, newSolns) =
        if ( not $ fal `lleq` al')
        then let
            theMap = Map.insert l' (latticeJoin fal al') currentSolns
            thePairs = map (\lNeighbour -> (l', lNeighbour) ) $ edgeMap info l'
          in (thePairs, theMap)
        else ([], currentSolns)
      in iterateSolns newSolns (newPairs ++ rest)








