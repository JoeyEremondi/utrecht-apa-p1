{-# LANGUAGE DeriveFunctor, UndecidableInstances, FlexibleInstances, StandaloneDeriving #-}
module Optimize.RelevantDefs (getRelevantDefs) where

import           AST.Annotation             (Annotated (..))
--import qualified AST.Expression.Canonical   as Canon
import           AST.Expression.General
import qualified AST.Module                 as Module
import qualified AST.Pattern                as Pattern
import qualified AST.Variable as Variable
import           Control.Monad
import qualified Data.List                  as List
import qualified Data.Map                   as Map hiding ((!))
import qualified Data.Set                   as Set
import           Elm.Compiler.Module
import           Optimize.Traversals


import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.EmbellishedMonotone
import           Optimize.Types

import Debug.Trace (trace)

import Optimize.ControlFlow

--How long do we let our call strings be?
contextDepth = 0

insertAll :: Ord k => [(k,a)] -> Map.Map k a -> Map.Map k a
insertAll pairs theMap = foldr (\(k,a) m -> Map.insert k a m) theMap pairs  



getFreeVars :: [ControlNode] ->  [VarPlus]
getFreeVars nodes = let
    freeVars = Set.toList $ foldr (
      \ lnode varsSoFar -> let
        thisLevelVars = case lnode of
          (Assign v _ ) -> [v]
          (AssignParam v1 v2 _) -> [v1, v2]
          _ -> []
      in varsSoFar `Set.union` (Set.fromList thisLevelVars)
      ) Set.empty nodes
  in  freeVars

    


--Give the list of definitions  
getRelevantDefs
  :: LabeledExpr
  -> Maybe (ProgramInfo LabelNode,
           Map.Map LabelNode (Set.Set (VarPlus, Maybe Label)),
           [LabelNode])
getRelevantDefs  eAnn =
  let
    --TODO add info for external calls!
    maybeInfo = do
      let expDict = labelDict eAnn
      --let initalEnv = globalEnv eAnn
      let defs = defsFromModuleExpr eAnn
      --let (A _ (Let defs _)) = eAnn
      let fnLabels = map (\(GenericDef _ (A (_, l, _ ) _) _) -> l ) defs
      let fnInfo = trace ("#####Fn labels " ++ show fnLabels  ) foldr (\(GenericDef (Pattern.Var n) fnDef _ ) finfo ->
              Map.insert (nameToCanonVar n)
              (FunctionInfo
               (getArity fnDef)
               (map (\pat -> FormalParam pat (getLabel fnDef) ) (functionArgPats fnDef)) 
               (ProcEntry fnDef)
               (ProcExit fnDef)
               (Just $ getLabel fnDef)
              ) finfo) Map.empty defs
      let fnBodies = map (\(GenericDef _ fnDef _ ) -> functionBody fnDef) defs
      (headDicts, tailDicts, edgeListList ) <- unzip3 `fmap` forM fnBodies (allExprEdges fnInfo)
      let headDict = Map.unions headDicts
      let tailDict = Map.unions tailDicts
      let targetNodes = map (\n -> ProcExit n ) fnLabels
      functionEdgeListList <- forM defs (functionDefEdges (headDict, tailDict))
      let entryEdges = [[(GlobalEntry, ProcEntry body)|
                         (GenericDef (Pattern.Var n) body _ ) <- defs ]]
      let edges = concat $ edgeListList ++ functionEdgeListList ++ entryEdges
      --edges = concat `fmap` edgeListList
      let allNodes = concat [[x,y] | (x,y) <- edges] --TODO nub?
      let progInfo =  makeProgramInfo edges
      let targetNodes = map (\n -> ProcExit n ) fnLabels
      trace ( "All edges " ++ (show (labelPairs progInfo ) ) ) $
        return (progInfo, allNodes, expDict, targetNodes, fnInfo)
  in case maybeInfo of
    Nothing -> Nothing
    Just (pinfo, allNodes, expDict, targetNodes, fnInfo) ->
      let
        reachMap = callGraph eAnn
        domain = map (\d -> map Call d) $ contextDomain contextDepth reachMap
        freeVars = getFreeVars allNodes
        iotaVal = Set.fromList [ (x, Nothing) | x <- freeVars]
        ourLat = embellishedRD domain  iotaVal
        --ourLat = reachingDefsLat iotaVal
        --(_, theDefsHat) = minFP ourLat transferFun pinfo
        (_, theDefsHat) = minFP ourLat (liftedTransfer iotaVal) pinfo
        theDefs = trace ("\ngot fp defs" ++ show theDefsHat ) $ Map.map (\(EmbPayload _ lhat) -> lhat []) theDefsHat
        --theDefs = trace ("!!!!!Reaching (not relevant) defs: " ++ show theDefsHat ) $ theDefsHat
        relevantDefs = Map.mapWithKey
                       (\x (ReachingDefs s) ->
                         Set.filter (isExprRef fnInfo expDict x) s) theDefs
      in trace ("TheDefs " ++ show theDefs )$ Just (pinfo, relevantDefs, targetNodes)

instance Show (ProgramInfo LabelNode) where
  show (ProgramInfo { edgeMap = pinfo_edgeMap,
                      allLabels = pinfo_allLabels,
                      labelPairs = pinfo_labelPairs,
                      isExtremal = pinfo_isExtremal }) =
    show pinfo_allLabels ++ show pinfo_labelPairs

isExprRef
  :: Map.Map Var FunctionInfo
  -> Map.Map Label LabeledExpr
  -> LabelNode
  -> (VarPlus, Maybe Label )
  -> Bool
isExprRef fnInfo exprs lnode (vplus, Just _) = let
    e = case (exprs `mapGet` (getNodeLabel lnode)) of
      (A _ (Let defs body)) -> body --We only look for refs in the body of a let
      ex -> ex
  in case vplus of
      NormalVar v defLabel -> expContainsVar e v 
      IntermedExpr l ->  expContainsLabel e l
      FormalReturn v ->
        --check if we reference the function called --TODO more advanced?
        (expContainsVar e v) || case (lnode, topFnLabel `fmap` Map.lookup v fnInfo) of
          (ProcExit l1, Just ( Just l2)) -> l1 == l2
          (Return v2 _, _ ) -> v == v2
          _ -> False
        
      ActualParam l -> expContainsLabel e l
      FormalParam pat _ -> or $ map (expContainsVar e) $ getPatternVars pat
isExprRef _ _ _ _ = False --If not in "Just" form, we ignore, since is uninitialized variable

makeProgramInfo :: [ControlEdge] -> ProgramInfo LabelNode
makeProgramInfo edgeList = let
    --first fmap is over labels, second is over pair
    getLab = (\(A (_,l,_) _) -> l)
    labelEdges :: [(LabelNode, LabelNode)]
    labelEdges = List.nub $ map (\(node1, node2) -> (fmap getLab node1, fmap getLab node2)) edgeList
    allLabels = List.nub $ concat $ [[n,n'] | (n,n') <- labelEdges]
    initialEdgeMap = Map.fromList $ zip allLabels $ repeat []
    edgeMap = foldr (\(l1, l2) env -> Map.insert l1 ([l2] ++ (env `mapGet` l1)  ) env) initialEdgeMap labelEdges
    edgeFn = (\node ->  edgeMap `mapGet` node)
    isExtremal (GlobalEntry) = True
    isExtremal _ = False --TODO entry or exit? Forward or backward?
  in ProgramInfo edgeFn allLabels labelEdges isExtremal

type RDef = (VarPlus, Maybe Label) 

newtype ReachingDefs = ReachingDefs (Set.Set RDef)
                      deriving (Eq, Ord, Show)

--TODO check this
reachingDefsLat :: Set.Set RDef -> Lattice ReachingDefs
reachingDefsLat iotaVal =  Lattice {
  latticeBottom = ReachingDefs (Set.empty),
  latticeJoin  = (\(ReachingDefs l1) ((ReachingDefs l2)) ->
    ReachingDefs (l1 `Set.union` l2)),
  iota = ReachingDefs iotaVal,
  lleq = \(ReachingDefs l1) (ReachingDefs l2) ->
    l1 `Set.isSubsetOf` l2,
  flowDirection = ForwardAnalysis --TODO forward or back?
  }


removeKills :: LabelNode -> Set.Set RDef -> Set.Set RDef
removeKills (Assign var _label) aIn = Set.filter (not . isKilled) aIn
  where isKilled (setVar, _setLab) = (setVar == var)
--Return is a special case, because there's an implicit unnamed variable we write to
--removeKills (Return _fnVar label) aIn = Set.filter (not . isKilled) aIn
--  where isKilled (setVar, _setLab) = (setVar == IntermedExpr label)
removeKills (AssignParam var _ _label) aIn = Set.filter (not . isKilled) aIn
  where isKilled (setVar, _setLab) = (setVar == var)
removeKills _ aIn = aIn

--TODO special case for return in ref-set

gens :: LabelNode -> Set.Set RDef
gens (Assign var label) = Set.singleton (var, Just label)
gens (AssignParam var _ label) = Set.singleton (var, Just label)
gens _ = Set.empty



--Transfer function for reaching definitions, we find the fixpoint for this
transferFun :: Map.Map LabelNode ReachingDefs -> LabelNode -> ReachingDefs -> ReachingDefs
transferFun labMap cfgNode (ReachingDefs aIn) =
  ReachingDefs $ (removeKills cfgNode aIn) `Set.union` (gens cfgNode)


genericDefVars :: GenericDef a Var -> [Var]
genericDefVars (GenericDef p _ _) = getPatternVars p



embellishedRD
  :: [[LabelNode]]
  -> Set.Set RDef
  -> Lattice (EmbPayload LabelNode ReachingDefs)
embellishedRD domain iotaVal  =
  let
    lat = (reachingDefsLat iotaVal)
  in trace ("Lifting with domain "  ++ show domain)$ liftToEmbellished domain (ReachingDefs iotaVal) lat

returnTransfer :: (LabelNode, LabelNode) -> (ReachingDefs, ReachingDefs) -> ReachingDefs
returnTransfer (lc, lr) (ReachingDefs aCall, ReachingDefs  aRet ) =
  ReachingDefs $ (removeKills lr (removeKills lc (aCall `Set.union` aRet )))
    `Set.union` (gens lc) `Set.union` (gens lr) 

liftedTransfer
  :: Set.Set RDef
  -> Map.Map LabelNode (EmbPayload LabelNode ReachingDefs)
  -> LabelNode
  -> (EmbPayload LabelNode  ReachingDefs)
  -> (EmbPayload LabelNode  ReachingDefs)
liftedTransfer iotaVal = liftToFn contextDepth (reachingDefsLat iotaVal) transferFun returnTransfer
