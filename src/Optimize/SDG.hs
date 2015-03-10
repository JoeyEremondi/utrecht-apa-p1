{-# LANGUAGE RecordWildCards #-}
module Optimize.SDG (removeModuleDeadCode) where

import           AST.Annotation             (Annotated (..))
import qualified AST.Expression.Canonical   as Canon
import           AST.Expression.General
import qualified AST.Module                 as Module
import qualified AST.Pattern                as Pattern
import           Control.Monad
import qualified Data.List                  as List
import qualified Data.Map                   as Map hiding ((!))
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

import Debug.Trace (trace)


data SDGNode = SDGLabel Label | SDGFunction LabelNode
  deriving (Eq, Ord, Show)

--The system dependence graph
newtype SDG = SDG {unSDG :: Set.Set SDGNode}
  deriving (Eq, Ord, Show)

makeTargetSet :: Set.Set LabelNode -> Set.Set SDGNode
makeTargetSet = Set.map (SDGLabel . getNodeLabel)

forwardSliceLattice :: Set.Set SDGNode -> Lattice SDG
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
  -> Map.Map SDGNode (EmbPayload SDGNode SDG)
  -> SDGNode
  -> EmbPayload SDGNode SDG
  -> EmbPayload SDGNode SDG
transferFun Lattice{..} resultDict lnode lhat@(EmbPayload domain pl) = case lnode of
  SDGLabel l -> lhat
  SDGFunction (Call l) -> EmbPayload domain (\d -> case d of
    [] -> latticeBottom
    lc:d' -> pl d')
  SDGFunction (Return fn l) -> let 
      (EmbPayload domain2 lcall) = resultDict `mapGet` (SDGFunction $ Call l)
    in EmbPayload (domain ++ domain2) $ \d ->
     (lcall d) `latticeJoin` (pl ((SDGFunction $ Call l):d ) )    


--Go through our CFG and determine if an edge is a control-flow edges
--to go in our call-graph
isFunctionEdge :: (LabelNode, LabelNode) -> Bool
isFunctionEdge edge = case edge of
  (Call _, ProcEntry _ ) -> True
  (ProcExit _, Return _ _ ) -> True
  _ -> False

makeFunctionEdge :: (LabelNode, LabelNode) -> (SDGNode, SDGNode)
makeFunctionEdge (n1, n2) = (SDGFunction n1, SDGFunction n2) 

sdgProgInfo
  :: [Name]
  -> LabeledExpr
  -> Maybe (ProgramInfo SDGNode, [SDGNode])
sdgProgInfo names eAnn = do
    (reachDefInfo, relevantDefs, targetNodes) <- getRelevantDefs eAnn
    --targetNodes <- getTargetNodes names eAnn
    let callEdges =
          map makeFunctionEdge $ filter isFunctionEdge (labelPairs reachDefInfo)
    let controlEdges = [] --TODO need control flow edges?
    let testEdges = Map.elems $ Map.mapWithKey
            (\n rdSet -> [(n,  def) | (_, Just def) <- (Set.toList rdSet)] ) relevantDefs
    let relevantDefEdges =
          concat $ Map.elems $ Map.mapWithKey
            (\n rdSet -> [(n,  def) | (_, Just def) <- (Set.toList rdSet)] ) relevantDefs
    --If n1 depends on def at label lab, then we have lab -> n1 as dependency
    --TODO is this right?
    let dataEdges = map (\(n1, lab) -> (SDGLabel lab, SDGLabel $ getNodeLabel n1)  ) relevantDefEdges
    let allEdges = trace ("Got relevant defs " ++ show relevantDefs) callEdges ++ controlEdges ++ dataEdges
    let sdgTargets = trace ("SDG Edges: " ++ show allEdges) $ makeTargetSet $ Set.fromList targetNodes
    let pinfo =
          ProgramInfo {
            edgeMap = \lnode -> [l2 | (l1, l2) <- allEdges, l1 == lnode], --TODO make faster
            allLabels = List.nub $ concat $ [[l1, l2] | (l1, l2) <- allEdges ],
            labelPairs = allEdges,
            isExtremal = \lnode -> lnode `Set.member` sdgTargets
          }
    
    return (pinfo, Set.toList sdgTargets)

setFromEmb :: EmbPayload SDGNode SDG -> Set.Set SDGNode
setFromEmb (EmbPayload _ lhat) = unSDG $ lhat []

removeDeadCode :: [Name] -> Canon.Expr -> Canon.Expr
removeDeadCode targetVars e = case dependencyMap of
  Nothing -> error "Failed getting data Dependencies"
  Just (depMap, targetNodes) -> trace ("Got depMap " ++ show depMap) $ toCanonical
    $ removeDefs (toDefSet depMap targetNodes) eAnn --TODO
  where
    eAnn = annotateCanonical (Map.empty)  (Label []) e
    toDefSet depMap targetNodes = trace "Makign def set " $ let
        defsReachingTargets =
          trace ( "DefsReachingTargets " ++ (show depMap ) ) $ Set.unions [setFromEmb (depMap `mapGet` tnode) | tnode <- targetNodes]
      in defsReachingTargets
    dependencyMap = do
      (pinfo, targetNodes) <- trace "Got SDG info" $  sdgProgInfo targetVars eAnn
      let (_,defMap) =
            minFP
              (embForwardSliceLat $ Set.fromList targetNodes)
              (transferFun $ forwardSliceLattice $ Set.fromList targetNodes) pinfo 
      return $  (defMap, targetNodes)
    removeDefs defSet (A ann (Let defs body)) =
      A ann $ Let (map (\(GenericDef pat body ty) -> GenericDef pat (removeDefsInBody defSet body) ty )
           defs) body  
    removeDefsInBody defSet = trace ("Removing with def set " ++ show defSet ) $
      tformEverywhere (\(A ann@(_,label,_) e) ->
        case e of
          Let defs body -> A ann $ Let (filter (defIsRelevant defSet label) defs) body
          _ -> A ann e )
    defIsRelevant defSet label (GenericDef pat expr ty) = let
        definedVars = getPatternVars pat
         --We want one of these assignments to be in the relevant set
        assignToLookFor = {-Assign (NormalVar definedVars)-}SDGLabel  label
      in assignToLookFor `Set.member` defSet

   

--TODO label definitions, not Let statements

removeModuleDeadCode :: ModuleOptFun
removeModuleDeadCode modName (modul, iface) = let
    isValue value = case value of
      Variable.Value s -> True
      _ -> False
    valToName (Variable.Value s) = Name [s]
    names = map valToName $ filter isValue $ Module.iExports iface  
  in (tformModule (removeDeadCode names) modul, iface)
