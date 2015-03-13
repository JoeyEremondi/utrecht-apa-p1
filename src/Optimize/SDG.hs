{-# LANGUAGE RecordWildCards #-}
module Optimize.SDG (removeModuleDeadCode) where

import           AST.Annotation               (Annotated (..))
import qualified AST.Expression.Canonical     as Canon
import           AST.Expression.General
import qualified AST.Module                   as Module
import qualified AST.Pattern                  as Pattern
import           Control.Monad
import qualified Data.List                    as List
import qualified Data.Map                     as Map hiding ((!))
import qualified Data.Set                     as Set
import           Elm.Compiler.Module
import           Optimize.Traversals

import qualified AST.Variable                 as Variable

import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.Types

import qualified AST.Variable                 as Var

import           Optimize.ControlFlow         hiding (trace)
import           Optimize.EmbellishedMonotone
import           Optimize.RelevantDefs

--import Optimize.Reachability (reachabilityMap)

import           Debug.Trace                  (trace)
--trace _ x = x
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
  liftToEmbellished domain (SDG startDefs) (forwardSliceLattice startDefs)

--Our transfer funciton is basically the identity,
--With the necessary lifting dealing with function return and call
--TODO is this right?
transferFun
  :: Lattice SDG
  -> Map.Map SDGNode (EmbPayload SDGNode SDG)
  -> SDGNode
  -> EmbPayload SDGNode SDG
  -> EmbPayload SDGNode SDG
transferFun lat@Lattice{..} resultDict lnode lhat@(EmbPayload (domain, pl)) = case lnode of
  SDGFunction (Call l) -> EmbPayload (domain, (\d -> case d of
    [] -> latticeBottom
    lc:d' -> let
        possibleEnds = [ldom | ldom <- domain, (take contextDepth (lc:ldom)) == (lc:d') ]
      in joinAll lat [pl dPoss | dPoss <- possibleEnds]) )
  SDGFunction (Return fn l) -> let
      (EmbPayload (domain2, lcall)) = resultDict `mapGet` (SDGFunction $ Call l)
    in EmbPayload (domain,  \d ->
     (lcall d) `latticeJoin` (pl ((SDGFunction $ Call l):d) ) )
  _ -> lhat

transferFun Lattice{..} resultDict lnode lhat@(EmbPayload (domain, pl)) = lhat

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
  :: Map.Map Var FunctionInfo
  -> [Name]
  -> LabeledExpr
  -> Maybe (ProgramInfo SDGNode, [SDGNode])
sdgProgInfo initFnInfo names eAnn = do
    (reachDefInfo, relevantDefs, targetNodes) <- getRelevantDefs initFnInfo  eAnn
    --targetNodes <- getTargetNodes names eAnn
    let callEdges =
          map makeFunctionEdge $ filter isFunctionEdge (labelPairs reachDefInfo)
    let controlEdges = [] --TODO need control flow edges?s
    let dataEdges =
          concat $ Map.elems $ Map.mapWithKey
            (\n rdSet -> [(SDGDef var def, toSDG n) | (var,  def) <- (Set.toList rdSet)] ) relevantDefs
    let originalLabels = map toSDG $ Map.keys relevantDefs
    --If n1 depends on def at label lab, then we have lab -> n1 as dependency
    --TODO is this right?
    --let dataEdges = map (\(n1, lab) -> (SDGLabel lab, toSDG n1)  ) relevantDefEdges
    let allEdges =  callEdges ++ controlEdges ++ dataEdges
    let sdgTargets = trace ("SDG Edges " ++ show allEdges )$ makeTargetSet $ Set.fromList targetNodes
    let pinfo =
          ProgramInfo {
            edgeMap = \lnode -> [l2 | (l1, l2) <- allEdges, l1 == lnode], --TODO make faster
            allLabels = List.nub $ originalLabels ++ ( concat $ [[l1, l2] | (l1, l2) <- allEdges ]),
            labelPairs = allEdges,
            isExtremal = \lnode -> let
                isTarget = lnode `Set.member` sdgTargets
              in isTarget
          }

    return (pinfo, Set.toList sdgTargets)

setFromEmb :: EmbPayload SDGNode SDG -> Set.Set SDGNode
setFromEmb (EmbPayload (_, lhat)) = unSDG $ lhat []



removeDeadCode
  :: Map.Map Var FunctionInfo
    -> [Name]
    -> Canon.Expr
    -> Canon.Expr
removeDeadCode initFnInfo targetVars e = case dependencyMap of
  Nothing -> trace "!!! Couldn't Optimize" e
  Just (depMap, targetNodes) -> trace "Opt Success" $ toCanonical
       $ removeDefs targetNodes depMap eAnn
    -- $ removeDefs (toDefSet depMap targetNodes) eAnn --TODO
  where
    eAnn = annotateCanonical (Map.empty)  (Label 1) e
    dependencyMap = do
      (pinfo, targetNodes) <- sdgProgInfo initFnInfo targetVars eAnn
      let reachMap = callGraph eAnn
      let domain = map (\d -> map (\l -> SDGFunction (Call l)) d ) $ contextDomain contextDepth reachMap
      let (_,embDefMap) =
            minFP --(forwardSliceLattice (Set.fromList targetNodes)) (\_ _ x -> x ) pinfo
              (embForwardSliceLat
                 (domain) $ Set.fromList targetNodes)
               (transferFun $ forwardSliceLattice $ Set.fromList targetNodes) pinfo
      let defMap = Map.map (\(EmbPayload (_, lhat)) -> lhat []) embDefMap
      return $  (defMap, targetNodes)

--Given a set of target nodes, a map from nodes to other nodes depending on that node,
--And a module's expression, traverse the tree and remove unnecessary Let definitions
removeDefs
  :: [Optimize.SDG.SDGNode]
  -> Map.Map SDGNode SDG
  -> LabeledExpr
  -> LabeledExpr
removeDefs targetNodes depMap eAnn =
      removeDefsMonadic targetNodes depMap
      $ tformModEverywhere (\(A ann@(_,defLab,_env) eToTrans) ->
        case eToTrans of
          Let defs defBody -> let
              newDefs = (filter (defIsRelevant defLab targetNodes depMap ) defs)
             in A ann $ Let (newDefs) defBody
          _ -> A ann eToTrans ) eAnn

removeDefsMonadic
  :: [Optimize.SDG.SDGNode]
  -> Map.Map SDGNode SDG
  -> LabeledExpr
  -> LabeledExpr
removeDefsMonadic targetNodes depMap eAnn = trace ("!!Removing monadic defs  \n\n" ) $ case eAnn of
  (A ann (Let defs body)) ->
    let
      newDefs = (cleanDefs defs)
      newBody = removeDefsMonadic targetNodes depMap body
    in (A ann $ Let newDefs newBody)
  _ -> eAnn
  where
      cleanDefs defList =
        map
        (\d@(GenericDef pat body ty) -> let
          newBody =
            if (trace ("\n Is Statement? " ++ show (isStateMonadFn ty)) $ isStateMonadFn ty)
            then (monadRemoveStatements (getLabel eAnn) targetNodes depMap (functionBody body ))
            else body
        in GenericDef pat newBody ty) defList


getAnn (A a _) = a

--Given a list of target nodes,
-- a mapping of nodes to nodes they are relevant to (result of our FP iteration)
-- and a Definition, return true if we should keep the definition
monadRemoveStatements :: Label -> [SDGNode] -> Map.Map SDGNode SDG -> LabeledExpr -> LabeledExpr
monadRemoveStatements _defLabel targetNodes reachedNodesMap monadBody = trace "!!!MonadRemove"$
  let
    op = Var.Canonical (Var.Module ["State", "Escapable"] ) ("andThen")
    (patStatements, lastStmt) = sequenceMonadic monadBody
    --patLabels = map snd patStatements
    --allStatements = (map fst patStatements) ++ [lastStmt]

    newList = filter
      (\(stmt, (_,_)) -> let
          --TODO check, is this right? Why don't we look at pattern?
           ourAssigns = [(SDGDef var compLab) |
                                     (SDGDef var compLab)<-Map.keys reachedNodesMap,
                                     compLab == getLabel stmt]--TODO make faster
           reachedNodes = Set.unions $ map
             (\varNode -> case (reachedNodesMap `mapGet` varNode) of
                    x -> unSDG x) ourAssigns
           isRel = not $ Set.null $ (Set.fromList targetNodes) `Set.intersection` reachedNodes
         in isRel ) patStatements
    reAssemble [] accum = accum
    reAssemble ((stmt, (pat, expr)) : rest) accum =
      reAssemble rest (A (getAnn expr) $ Binop op stmt (A (getAnn accum) $ Lambda pat accum))
  in reAssemble (reverse newList) lastStmt



--Given a list of target nodes,
-- a mapping of nodes to nodes they are relevant to (result of our FP iteration)
-- and a Definition, return true if we should keep the definition
defIsRelevant :: Label -> [SDGNode] -> Map.Map SDGNode SDG -> LabelDef -> Bool
defIsRelevant defLabel targetNodes reachedNodesMap (GenericDef pat expr _ty) = let
        definedVars = getPatternVars pat
        definedVarPlusses = map (\v -> NormalVar v defLabel) definedVars
        nodesForDefs = map (\var -> SDGDef var (getLabel expr)) definedVarPlusses
        reachedNodes = Set.unions $
          map (\varNode -> case (reachedNodesMap `mapGet` varNode) of
                  x -> unSDG x) nodesForDefs
                  -- EmbPayload _ lhat -> unSDG $ lhat []) nodesForDefs
        isRel = not $ Set.null $ (Set.fromList targetNodes) `Set.intersection` reachedNodes
      in isRel



--TODO label definitions, not Let statements

removeModuleDeadCode :: ModuleOptFun
removeModuleDeadCode otherIfaces modName  (modul, iface) = trace (show modName) $ let
    fnInfo = interfaceFnInfo otherIfaces
    isValue value = case value of --TODO remove
      Variable.Value s -> True
      _ -> False
    valToName (Variable.Value s) = Name [s]
    names = map valToName $ filter isValue $ Module.iExports iface
  in (tformModule (removeDeadCode fnInfo names) modul, iface)
