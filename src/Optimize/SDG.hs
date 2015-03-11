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

--import Optimize.Reachability (reachabilityMap)

import Debug.Trace (trace)

--How deep we go in our call strings for context
contextDepth = 2


data SDGNode = SDGDef VarPlus Label | SDGLabel Label | SDGFunction LabelNode
  deriving (Eq, Ord, Show)

--The system dependence graph
newtype SDG = SDG {unSDG :: Set.Set SDGNode}
  deriving (Eq, Ord, Show)

makeTargetSet :: Set.Set LabelNode -> Set.Set SDGNode
makeTargetSet = Set.map toSDG 

toSDG :: LabelNode -> SDGNode
toSDG lnode = case lnode of
  Assign var label -> SDGDef var label
  _ -> SDGLabel $ getNodeLabel lnode
  

forwardSliceLattice :: Set.Set SDGNode -> Lattice SDG
forwardSliceLattice startDefs = Lattice {
  --latticeTop :: a
  latticeBottom = SDG Set.empty ,
  latticeJoin = \(SDG s1) (SDG s2) -> SDG $ Set.union s1 s2,
  iota = SDG startDefs, --Extremal value for our analysis
  lleq = \(SDG s1) (SDG s2) -> s1 `Set.isSubsetOf` s2,
  flowDirection = BackwardAnalysis
  }

embForwardSliceLat domain startDefs  =
  liftToEmbellished domain (EmbPayload domain $ \d -> case d of
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
transferFun lat@Lattice{..} resultDict lnode lhat@(EmbPayload domain pl) = case lnode of
  SDGFunction (Call l) -> EmbPayload domain (\d -> case d of
    [] -> latticeBottom
    lc:d' -> let
        possibleEnds = [ldom | ldom <- domain, (take contextDepth (lc:ldom)) == (lc:d') ]
      in joinAll lat [pl dPoss | dPoss <- possibleEnds])
  SDGFunction (Return fn l) -> let 
      (EmbPayload domain2 lcall) = resultDict `mapGet` (SDGFunction $ Call l)
    in EmbPayload (domain ++ domain2) $ \d ->
     (lcall d) `latticeJoin` (pl ((SDGFunction $ Call l):d ) )
  _ -> lhat

transferFun Lattice{..} resultDict lnode lhat@(EmbPayload domain pl) = lhat

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
    let controlEdges = [] --TODO need control flow edges?s
    let dataEdges =
          concat $ Map.elems $ Map.mapWithKey
            (\n rdSet -> [(SDGDef var def, toSDG n) | (var, Just def) <- (Set.toList rdSet)] ) relevantDefs
    let originalLabels = map toSDG $ Map.keys relevantDefs
    --If n1 depends on def at label lab, then we have lab -> n1 as dependency
    --TODO is this right?
    --let dataEdges = map (\(n1, lab) -> (SDGLabel lab, toSDG n1)  ) relevantDefEdges
    let allEdges = trace ("Got relevant defs " ++ show relevantDefs) callEdges ++ controlEdges ++ dataEdges
    let sdgTargets = trace ("SDG Edges: " ++ show allEdges) $ makeTargetSet $ Set.fromList targetNodes
    let pinfo =
          ProgramInfo {
            edgeMap = \lnode -> [l2 | (l1, l2) <- allEdges, l1 == lnode], --TODO make faster
            allLabels = List.nub $ originalLabels ++ ( concat $ [[l1, l2] | (l1, l2) <- allEdges ]),
            labelPairs = allEdges,
            isExtremal = \lnode -> let
                isTarget = lnode `Set.member` sdgTargets
              in trace ("Is Extremal? " ++ show lnode ++ " targets " ++ show sdgTargets ++ "ismember " ++ show isTarget ) $ isTarget
          }
    
    return (pinfo, Set.toList sdgTargets)

setFromEmb :: EmbPayload SDGNode SDG -> Set.Set SDGNode
setFromEmb (EmbPayload _ lhat) = unSDG $ lhat []



removeDeadCode
  :: [Name]
    -> Canon.Expr
    -> Canon.Expr
removeDeadCode  targetVars e = case dependencyMap of
  Nothing -> error "Failed getting data Dependencies"
  Just (depMap, targetNodes) -> trace ("Got depMap " ++ show depMap) $ toCanonical
       $ removeDefs targetNodes depMap eAnn 
    -- $ removeDefs (toDefSet depMap targetNodes) eAnn --TODO
  where
    eAnn = annotateCanonical (Map.empty)  (Label []) e
    dependencyMap = do
      (pinfo, targetNodes) <- sdgProgInfo targetVars eAnn
      let reachMap = callGraph eAnn
      let domain = map (\d -> map (\l -> SDGFunction (Call l)) d ) $ contextDomain contextDepth reachMap
      let (_,embDefMap) =
            minFP
              (embForwardSliceLat
                 (domain) $ Set.fromList targetNodes)
              (transferFun $ forwardSliceLattice $ Set.fromList targetNodes) pinfo
      let defMap = Map.map (\(EmbPayload _ lhat) -> lhat []) embDefMap 
      return $  (defMap, targetNodes)

--Given a set of target nodes, a map from nodes to other nodes depending on that node,
--And a module's expression, traverse the tree and remove unnecessary Let definitions
removeDefs targetNodes depMap (A ann (Let defs body)) =
      A ann $ Let (map (\(GenericDef pat bdy ty) -> GenericDef pat (removeDefsInBody targetNodes depMap bdy) ty )
           defs) body  


removeDefsInBody targetNodes depMap = trace ("Removing with dep depMap " ++ show depMap ) $
      tformEverywhere (\(A ann@(_,lab,_) eToTrans) ->
        case eToTrans of
          Let defs body -> A ann $ Let (filter (defIsRelevant targetNodes depMap ) defs) body
          _ -> A ann eToTrans )
    --TODO treat each def as separate



--Given a list of target nodes,
-- a mapping of nodes to nodes they are relevant to (result of our FP iteration)
-- and a Definition, return true if we should keep the definition
defIsRelevant :: [SDGNode] -> Map.Map SDGNode SDG -> LabelDef -> Bool
defIsRelevant targetNodes reachedNodesMap def@(GenericDef pat expr _ty) = let
        definedVars = getPatternVars pat
        definedVarPlusses = map (\v -> NormalVar $  v) definedVars
        nodesForDefs = map (\var -> SDGDef var (getLabel expr)) definedVarPlusses
        reachedNodes = Set.unions $
          map (\varNode -> case (reachedNodesMap `mapGet` varNode) of
                  x -> unSDG x) nodesForDefs
                  -- EmbPayload _ lhat -> unSDG $ lhat []) nodesForDefs
        isRel = not $ Set.null $ (Set.fromList targetNodes) `Set.intersection` reachedNodes
      in isRel

   

--TODO label definitions, not Let statements

removeModuleDeadCode :: ModuleOptFun
removeModuleDeadCode modName (modul, iface) = let
    
    isValue value = case value of--TODO remove
      Variable.Value s -> True
      _ -> False
    valToName (Variable.Value s) = Name [s]
    names = map valToName $ filter isValue $ Module.iExports iface
  in (tformModule (removeDeadCode names) modul, iface)
