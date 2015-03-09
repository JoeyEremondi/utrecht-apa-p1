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
import qualified Data.Map                   as Map
import qualified Data.Set                   as Set
import           Elm.Compiler.Module
import           Optimize.Traversals


import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.EmbellishedMonotone
import           Optimize.Types

import Optimize.ControlFlow

insertAll :: Ord k => [(k,a)] -> Map.Map k a -> Map.Map k a
insertAll pairs theMap = foldr (\(k,a) m -> Map.insert k a m) theMap pairs  



getFreeVars :: [ControlNode] ->  [VarPlus]
getFreeVars nodes = Set.toList $ foldr (
  \ lnode varsSoFar ->
    let thisLevelVars = case lnode of
          (Assign v _ ) -> [v]
          _ -> []
    in varsSoFar `Set.union` (Set.fromList thisLevelVars)
  ) Set.empty nodes

    
nameToCanonVar :: String -> Var
nameToCanonVar name = Variable.Canonical  Variable.Local name

--Give the list of definitions  
getRelevantDefs
  :: LabeledExpr
  -> Maybe (ProgramInfo LabelNode,
           Map.Map LabelNode (Set.Set (VarPlus, Maybe Label)),
           [LabelNode])
getRelevantDefs  eAnn =
  let
    --eAnn = annotateCanonical (Map.empty)  (Label []) e
    expDict = labelDict eAnn
    initalEnv = globalEnv eAnn
    (A _ (Let defs _)) = eAnn
    fnLabels = map functionLabel defs
    fnInfo =
      foldr (\(GenericDef (Pattern.Var n) body _ ) finfo ->
              Map.insert (nameToCanonVar n)
              (FunctionInfo
               (getArity body)
               (map (\pat -> FormalParam pat (getLabel body) ) (functionArgPats body)) 
               (ProcEntry eAnn)
               (ProcExit eAnn)
              ) finfo) Map.empty defs
    edgeListList = forM defs (\(GenericDef _ expr _) -> allExprEdges fnInfo expr)
    edges = concat `fmap` edgeListList
    maybeAllNodes = (\edgeList -> concat [[x,y] | (x,y) <- edgeList]) `fmap` edges --TODO nub?
    progInfo = makeProgramInfo `fmap` edges
    targetNodes = map (\n -> ProcExit n ) fnLabels
  in case (progInfo, maybeAllNodes) of
    (Nothing, _) -> Nothing
    (_, Nothing) -> Nothing
    (Just pinfo, Just allNodes) ->
      let
        freeVars = getFreeVars allNodes
        iotaVal = Set.fromList [ (x, Nothing) | x <- freeVars]
        ourLat = embellishedRD iotaVal
        (_, theDefsHat) = minFP ourLat (liftedTransfer iotaVal) pinfo
        theDefs = Map.map (\(EmbPayload _ lhat) -> lhat []) theDefsHat
        relevantDefs = Map.mapWithKey
                       (\x (ReachingDefs s) ->
                         Set.filter (isExprRef expDict x) s) theDefs
      in Just (pinfo, relevantDefs, targetNodes)


isExprRef
  :: Map.Map Label LabeledExpr
  -> LabelNode
  -> (VarPlus, Maybe Label )
  -> Bool
isExprRef exprs lnode (vplus, _) = let
    e = exprs Map.! (getNodeLabel lnode)
  in case vplus of
      NormalVar v -> or $ map (expContainsVar e) v 
      IntermedExpr l -> expContainsLabel e l
      FormalReturn v -> expContainsVar e v --check if we reference the function called --TODO more advanced?
      ActualParam l -> expContainsLabel e l
      FormalParam pat _ -> or $ map (expContainsVar e) $ getPatternVars pat

makeProgramInfo :: [ControlEdge] -> ProgramInfo LabelNode
makeProgramInfo edgeList = let
    --first fmap is over labels, second is over pair
    getLab = (\(A (_,l,_) _) -> l)
    labelEdges :: [(LabelNode, LabelNode)]
    labelEdges = List.nub $ map (\(node1, node2) -> (fmap getLab node1, fmap getLab node2)) edgeList
    allLabels = List.nub $ concat $ [[n,n'] | (n,n') <- labelEdges]
    edgeMap = foldr (\(l1, l2) env -> Map.insert l1 ([l2] ++ env Map.! l1) env) Map.empty labelEdges
    edgeFn = (\node -> edgeMap Map.! node)
    isExtremal (GlobalEntry) = True
    isExtremal _ = False --TODO entry or exit? Forward or backward?
  in ProgramInfo edgeFn allLabels labelEdges isExtremal

type RDef = (VarPlus, Maybe Label) 

newtype ReachingDefs = ReachingDefs (Set.Set RDef)
                      deriving (Eq, Ord)

--TODO check this
reachingDefsLat :: Set.Set RDef -> Lattice ReachingDefs
reachingDefsLat iotaVal =  Lattice {
  latticeBottom = ReachingDefs (Set.empty),
  latticeJoin  = (\(ReachingDefs l1) ((ReachingDefs l2)) ->
    ReachingDefs (l1 `Set.union` l2)),
  iota = ReachingDefs iotaVal,
  lleq = \(ReachingDefs l1) (ReachingDefs l2) ->
    l1 `Set.isSubsetOf` l2,
  flowDirection = BackwardAnalysis
  }



removeKills (Assign var label) aIn = Set.filter (not . isKilled) aIn
  where isKilled (setVar, setLab) = (setVar == var)
--Return is a special case, because there's an implicit unnamed variable we write to
removeKills (Return fnVar label) aIn = Set.filter (not . isKilled) aIn
  where isKilled (setVar, setLab) = (setVar == IntermedExpr label)
removeKills _ aIn = aIn

--TODO special case for return in ref-set

gens :: LabelNode -> Set.Set RDef
gens (Assign var label) = Set.singleton (var, Just label)
gens _ = Set.empty



--Transfer function for reaching definitions, we find the fixpoint for this
transferFun :: Map.Map LabelNode ReachingDefs -> LabelNode -> ReachingDefs -> ReachingDefs
transferFun labMap cfgNode (ReachingDefs aIn) =
  ReachingDefs $ (removeKills cfgNode aIn) `Set.union` (gens cfgNode)


genericDefVars :: GenericDef a Var -> [Var]
genericDefVars (GenericDef p _ _) = getPatternVars p



embellishedRD
  :: Set.Set RDef
  -> Lattice (EmbPayload [LabelNode] ReachingDefs)
embellishedRD iotaVal  =
  let
    lat = (reachingDefsLat iotaVal)
    liftedIota = EmbPayload [] (\ d -> case d of
                                   [] -> ReachingDefs iotaVal
                                   _ -> latticeBottom lat)
  in liftToEmbellished liftedIota lat

returnTransfer :: (LabelNode, LabelNode) -> (ReachingDefs, ReachingDefs) -> ReachingDefs
returnTransfer (lc, lr) (ReachingDefs aCall, ReachingDefs  aRet ) =
  ReachingDefs $ (removeKills lr (removeKills lc aCall))
    `Set.union` (gens lc) `Set.union` (gens lr) 

liftedTransfer
  :: Set.Set RDef
  -> Map.Map LabelNode (EmbPayload [LabelNode] ReachingDefs)
  -> LabelNode
  -> (EmbPayload [LabelNode]  ReachingDefs)
  -> (EmbPayload [LabelNode]  ReachingDefs)
liftedTransfer iotaVal = liftToFn (reachingDefsLat iotaVal) transferFun returnTransfer
