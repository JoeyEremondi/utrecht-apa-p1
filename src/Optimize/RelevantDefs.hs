{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE BangPatterns #-}
module Optimize.RelevantDefs (getRelevantDefs) where

import           AST.Annotation               (Annotated (..))
--import qualified AST.Expression.Canonical   as Canon
import           AST.Expression.General
import qualified AST.Module                   as Module
import qualified AST.Pattern                  as Pattern
import qualified AST.Variable                 as Variable
import           Control.Monad
import qualified Data.List                    as List
import qualified Data.HashMap.Strict                     as Map
import qualified Data.Map as NormalMap
import qualified Data.IntMap                     as IntMap
import qualified Data.Set                     as Set
import           Elm.Compiler.Module
import           Optimize.Traversals


import           Optimize.EmbellishedMonotone
import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.Types

import           AST.PrettyPrint              (pretty)
import           Text.PrettyPrint.HughesPJ    (render)

import qualified Data.HashSet as HSet
import Data.Hashable 

import           Optimize.ControlFlow         hiding (trace)
import qualified  Data.HashSet as HSet

import           Debug.Trace                  (trace)
--trace _ x = x

--How long do we let our call strings be?
contextDepth = 1

insertAll :: (Hashable k, Eq k) => [(k,a)] -> Map.HashMap k a -> Map.HashMap k a
insertAll pairs theMap = List.foldl' (\m (k,a) -> Map.insert k a m) theMap pairs



getFreeVars :: [LabelNode] ->  [VarPlus]
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
  :: NormalMap.Map Var FunctionInfo
  -> LabeledExpr
  -> Maybe (ProgramInfo LabelNode,
           Map.HashMap LabelNode (HSet.HashSet (VarPlus, Label)),
           [LabelNode])
getRelevantDefs  initFnInfo eAnn = trace "\nIn Relevant Defs!!!!" $
  let
    --TODO add info for external calls!
    maybeInfo = do
      let expDict = labelDict eAnn
      --let initalEnv = globalEnv eAnn
      let defs = defsFromModuleExpr eAnn
      --let (A _ (Let defs _)) = eAnn
      let fnLabels = map (\(GenericDef _ (A (_, l, _ ) _) _) -> l ) defs
      let fnInfo = trace ("#####Fn labels " ++ show fnLabels  ) foldr (\(GenericDef (Pattern.Var n) fnDef _ ) finfo ->
              NormalMap.insert (nameToCanonVar n)
              (FunctionInfo
               (getArity fnDef)
               (map (\pat -> FormalParam pat (getLabel fnDef) ) (functionArgPats fnDef))
               (ProcEntry fnDef)
               (ProcExit fnDef)
               (Just $ getLabel fnDef)
              ) finfo) initFnInfo defs
      (headDicts, tailDicts, edgeListList ) <- trace "Getting all edges" $ unzip3 `fmap` forM defs (allDefEdges fnInfo)
      let headDict = trace "Getting head dict" $ IntMap.unions headDicts
      let tailDict = IntMap.unions tailDicts
      functionEdgeListList <- forM defs (functionDefEdges (headDict, tailDict))
      let !initialNodes = [ProcEntry (getLabel body)| (GenericDef (Pattern.Var n) body _ ) <- defs ]
      let !controlEdges = concat $ edgeListList ++ functionEdgeListList
      let !edges = map (\(n1,n2) -> (getLabel `fmap` n1, getLabel `fmap` n2 ) ) controlEdges
      --edges = concat `fmap` edgeListList
      let !allNodes =  Set.toList $ Set.fromList $ List.foldl' (\l (x,y) -> [x,y] ++ l ) []  edges --TODO nub?
      let !progInfo =  makeProgramInfo (Set.fromList initialNodes) allNodes edges
      let !targetNodes = map (\n -> ProcExit n ) fnLabels
      return $! (progInfo, allNodes, expDict, targetNodes, fnInfo, fnLabels)
  in case maybeInfo of
    Nothing -> trace "Failed getting info" $ Nothing
    Just (pinfo, allNodes, expDict, targetNodes, fnInfo, fnLabels) ->
      let
        !intMap = Map.fromList $ zip allNodes [1..]
        labelInfo cnode = show  cnode
        nameMap = Map.mapWithKey
          (\node _ -> ("Node: " ++ labelInfo node ) ++ "\n\n" ++
            (render $ pretty $ (expDict IntMap.! ( getNodeLabel node) ) ) )  intMap
        reachMap = 
          callGraph eAnn
        domain = map (\d -> map Call d) $ contextDomain fnLabels contextDepth reachMap
        --freeVars = getFreeVars allNodes
        !iotaVal = HSet.fromList [] --TODO put back? -- [ (x, Nothing) | x <- freeVars]
        !ourLat = embellishedRD domain  iotaVal
        --ourLat = reachingDefsLat iotaVal
        --(_, theDefsHat) = minFP ourLat transferFun pinfo
        (_, !theDefsHat) = minFP ourLat (liftedTransfer iotaVal) pinfo
        theDefs = Map.map (\(EmbPayload (_, lhat)) -> lhat []) theDefsHat
        --theDefs = trace ("!!!!!Reaching (not relevant) defs: " ++ show theDefsHat ) $ theDefsHat
        relevantDefs = trace ("\n\nTheDefs \n\n" ++ (show theDefs) ++ "\n\n\n" ) $ Map.mapWithKey
                       (\x (ReachingDefs s) ->
                         HSet.filter (isExprRef fnInfo expDict x) s) theDefs
      in trace ("\n\nRelevant Defs \n\n" ++ show relevantDefs )$ Just (pinfo, relevantDefs, targetNodes)

instance Show (ProgramInfo LabelNode) where
  show (ProgramInfo { edgeMap = pinfo_edgeMap,
                      allLabels = pinfo_allLabels,
                      labelPairs = pinfo_labelPairs,
                      isExtremal = pinfo_isExtremal }) =
    show pinfo_allLabels ++ show pinfo_labelPairs

isExprRef
  :: NormalMap.Map Var FunctionInfo
  -> IntMap.IntMap LabeledExpr
  -> LabelNode
  -> (VarPlus, Label )
  -> Bool
isExprRef fnInfo exprs lnode (vplus,  _) = let
    e = case (exprs IntMap.! (getNodeLabel lnode)) of
      (A _ (Let defs body)) -> body --We only look for refs in the body of a let
      ex -> ex
  in case vplus of
      ExternalParam _ v -> expContainsVar e v
      Ref v -> expContainsVar e v --TODO special case for assign?
      NormalVar v _defLabel -> expContainsVar e v
      IntermedExpr l ->  expContainsLabel e l
      FormalReturn v ->
        --check if we reference the function called --TODO more advanced?
        (expContainsVar e v) || case (lnode, topFnLabel `fmap` NormalMap.lookup v fnInfo) of
          (ProcExit l1, Just ( Just l2)) -> l1 == l2
          (Return v2 _, _ ) -> v == v2
          _ -> False

      ActualParam l -> expContainsLabel e l
      FormalParam pat _ -> or $ map (expContainsVar e) $ getPatternVars pat
isExprRef _ _ _ _ = False --If not in "Just" form, we ignore, since is uninitialized variable

makeProgramInfo :: Set.Set LabelNode -> [LabelNode] -> [(LabelNode, LabelNode)] -> ProgramInfo LabelNode
makeProgramInfo initialNodes allLabels edgeList = let
    --first fmap is over labels, second is over pair
    --labelEdges = List.nub $ map (\(node1, node2) -> (fmap getLab node1, fmap getLab node2)) edgeList
    --allLabels = List.nub $ concat $ [[n,n'] | (n,n') <- edgeList]
    initialEdgeMap = Map.fromList $ zip allLabels $ repeat []
    edgeMap = foldr (\(l1, l2) env -> Map.insert l1 ([l2] ++ (env Map.! l1)  ) env) initialEdgeMap edgeList
    edgeFn = (\node ->  edgeMap Map.! node)
    isExtremal = (`Set.member` initialNodes)
  in ProgramInfo edgeFn allLabels edgeList isExtremal

type RDef = (VarPlus, Label)

instance Hashable RDef where
  hashWithSalt _ (_, label) = label

newtype ReachingDefs = ReachingDefs (HSet.HashSet RDef)
                      deriving ( Show)

instance Eq ReachingDefs where
  (ReachingDefs s1) == (ReachingDefs s2) = s1 == s2

--TODO check this
reachingDefsLat :: HSet.HashSet RDef -> Lattice ReachingDefs
reachingDefsLat iotaVal =
  let
    rdefJoin (ReachingDefs l1) (ReachingDefs l2) = ReachingDefs (l1 `HSet.union` l2)
    rdefLleq (ReachingDefs l1) (ReachingDefs l2) = HSet.null $ HSet.difference l1  l2

  in Lattice {
  latticeBottom = ReachingDefs (HSet.empty),
  latticeJoin  = rdefJoin,
  iota = ReachingDefs (HSet.empty), --TODO is this okay? --ReachingDefs iotaVal,
  lleq = rdefLleq,
  flowDirection = ForwardAnalysis --TODO forward or back?
  }


removeKills :: LabelNode -> HSet.HashSet RDef -> HSet.HashSet RDef
removeKills (Assign var _label) aIn = HSet.filter (notKilled) aIn
  where notKilled (!setVar, _setLab) = (setVar /= var)
--Return is a special case, because there's an implicit unnamed variable we write to
--removeKills (Return _fnVar label) aIn = Set.filter (not . isKilled) aIn
--  where isKilled (setVar, _setLab) = (setVar == IntermedExpr label)
removeKills (AssignParam var _ _label) aIn = HSet.filter (notKilled) aIn
  where notKilled (!setVar, _setLab) = (setVar /= var)
removeKills _ aIn = aIn

--TODO special case for return in ref-set

gens :: LabelNode -> HSet.HashSet RDef
gens (Assign !var !label) = HSet.singleton (var, label)
gens (AssignParam !var _ !label) = HSet.singleton (var, label)
gens (ExternalCall !v _) = HSet.singleton (FormalReturn v, externalCallLabel)
gens _ = HSet.empty



--Transfer function for reaching definitions, we find the fixpoint for this
transferFun :: Map.HashMap LabelNode ReachingDefs -> LabelNode -> ReachingDefs -> ReachingDefs
transferFun labMap cfgNode (ReachingDefs aIn) =
  ReachingDefs $ (removeKills cfgNode aIn) `HSet.union` (gens cfgNode)


genericDefVars :: GenericDef a Var -> [Var]
genericDefVars (GenericDef p _ _) = getPatternVars p



embellishedRD
  :: [[LabelNode]]
  -> HSet.HashSet RDef
  -> Lattice (EmbPayload LabelNode ReachingDefs)
embellishedRD domain iotaVal  =
  let
    lat = (reachingDefsLat iotaVal)
  in liftToEmbellished domain (ReachingDefs iotaVal) lat

returnTransfer :: (LabelNode, LabelNode) -> (ReachingDefs, ReachingDefs) -> ReachingDefs
returnTransfer (lc, lr) (ReachingDefs aCall, ReachingDefs  aRet ) =
  ReachingDefs $ (removeKills lr (removeKills lc (aCall `HSet.union` aRet )))
    `HSet.union` (gens lc) `HSet.union` (gens lr)

liftedTransfer
  :: HSet.HashSet RDef
  -> Map.HashMap LabelNode (EmbPayload LabelNode ReachingDefs)
  -> LabelNode
  -> (EmbPayload LabelNode  ReachingDefs)
  -> (EmbPayload LabelNode  ReachingDefs)
liftedTransfer iotaVal = liftToFn contextDepth (reachingDefsLat iotaVal) transferFun returnTransfer
