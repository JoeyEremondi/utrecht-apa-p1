{-# LANGUAGE RecordWildCards #-}
module Optimize.SDG (removeModuleDeadCode) where

import           AST.Annotation             (Annotated (..))
import qualified AST.Expression.Canonical   as Canon
import           AST.Expression.General
import qualified AST.Module                 as Module
import qualified AST.Pattern                as Pattern
import           Control.Monad
import qualified Data.List                  as List
import qualified Data.Map                   as Map
import qualified Data.Set                   as Set
import           Elm.Compiler.Module
import           Optimize.Traversals

import qualified AST.Variable as Variable

import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.Types

import Optimize.EmbellishedMonotone
import Optimize.ControlFlow
import Optimize.RelevantDefs



--The system dependence graph
newtype SDG = SDG {unSDG :: Set.Set LabelNode}

forwardSliceLattice :: Set.Set LabelNode -> Lattice SDG
forwardSliceLattice startDefs = Lattice {
  --latticeTop :: a
  latticeBottom = SDG Set.empty ,
  latticeJoin = \(SDG s1) (SDG s2) -> SDG $ Set.union s1 s2,
  iota = SDG startDefs, --Extremal value for our analysis
  lleq = \(SDG s1) (SDG s2) -> s1 `Set.isSubsetOf` s2,
  flowDirection = BackwardAnalysis
  }

embForwardSliceLat startDefs  =
  liftToEmbellished (EmbPayload [] $ \d -> case d of
                        [] -> SDG startDefs
                        _ -> SDG Set.empty) $ forwardSliceLattice startDefs

--Our transfer funciton is basically the identity,
--With the necessary lifting dealing with function return and call
--TODO is this right?
transferFun
  :: Lattice SDG
  -> Map.Map LabelNode (EmbPayload [LabelNode] SDG)
  -> LabelNode
  -> EmbPayload [LabelNode] SDG
  -> EmbPayload [LabelNode] SDG
transferFun Lattice{..} resultDict lnode lhat@(EmbPayload domain pl) = case lnode of
  Branch l -> lhat
  Assign var l -> lhat
  Call l -> EmbPayload domain (\d -> case d of
    [] -> latticeBottom
    lc:d' -> pl d')
  Return fn l -> let 
      (EmbPayload domain2 lcall) = resultDict Map.! (Call l)
    in EmbPayload (domain ++ domain2) $ \d ->
     (lcall d) `latticeJoin` (pl ((Call l):d ) )    
  ProcEntry l -> lhat
  ProcExit l -> lhat
  GlobalEntry -> lhat
  GlobalExit -> lhat

--Go through our CFG and determine if an edge is a control-flow edges
--to go in our call-graph
isFunctionEdge :: (LabelNode, LabelNode) -> Bool
isFunctionEdge edge = case edge of
  (Call _, ProcEntry _ ) -> True
  (ProcExit _, Return _ _ ) -> True
  _ -> False

sdgProgInfo
  :: [Name]
  -> LabeledExpr
  -> Maybe (ProgramInfo LabelNode, [LabelNode])
sdgProgInfo names eAnn = do
    (reachDefInfo, relevantDefs, targetNodes) <- getRelevantDefs eAnn
    --targetNodes <- getTargetNodes names eAnn
    let callEdges = filter isFunctionEdge (labelPairs reachDefInfo)
    let controlEdges = [] --TODO need control flow edges?
    let dataEdges = []
    let allEdges = callEdges ++ controlEdges ++ dataEdges
    let pinfo =
          ProgramInfo {
            edgeMap = \lnode -> [l2 | (l1, l2) <- allEdges, l1 == lnode], --TODO make faster
            allLabels = List.nub $ concat $ [[l1, l2] | (l1, l2) <- allEdges ],
            labelPairs = allEdges,
            isExtremal = \lnode -> lnode `elem` targetNodes
          }
    
    return (pinfo,targetNodes)

setFromEmb :: EmbPayload [LabelNode] SDG -> Set.Set LabelNode
setFromEmb (EmbPayload _ lhat) = unSDG $ lhat []

removeDeadCode :: [Name] -> Canon.Expr -> Canon.Expr
removeDeadCode targetVars e = case dependencyMap of
  Nothing -> e
  Just (depMap, targetNodes) -> toCanonical
    $ removeDefs (toDefSet depMap targetNodes) eAnn --TODO
  where
    eAnn = annotateCanonical (Map.empty)  (Label []) e
    toDefSet defMap targetNodes = let
        defsReachingTargets = Set.unions [setFromEmb (defMap Map.! tnode) | tnode <- targetNodes]
      in defsReachingTargets
    dependencyMap = do
      (pinfo, targetNodes) <- sdgProgInfo targetVars eAnn
      let (_,defMap) =
            minFP
              (embForwardSliceLat $ Set.fromList targetNodes)
              (transferFun $ forwardSliceLattice $ Set.fromList targetNodes) pinfo 
      return $  (defMap, targetNodes)
    removeDefs defSet =
      tformEverywhere (\(A ann@(_,label,_) e) ->
        case e of
          Let defs body -> A ann $ Let (filter (defIsRelevant defSet label) defs) body
          _ -> A ann e )
    defIsRelevant defSet label (GenericDef pat expr ty) = let
        definedVars = getPatternVars pat
         --We want one of these assignments to be in the relevant set
        assignToLookFor = Assign (NormalVar definedVars) label
      in assignToLookFor `Set.member` defSet

   

--TODO label definitions, not Let statements

removeModuleDeadCode
  :: PublicModule.Name
    -> (PublicModule.Module, PublicModule.Interface)
    -> (PublicModule.Module, PublicModule.Interface)
removeModuleDeadCode modName (modul, iface) =
  (removeDeadCode modul, iface)
