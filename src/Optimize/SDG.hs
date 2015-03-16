{-# LANGUAGE RecordWildCards #-}
module Optimize.SDG (removeModuleDeadCode) where

import           AST.Annotation               (Annotated (..))
import qualified AST.Expression.Canonical     as Canon
import           AST.Expression.General
import qualified AST.Module                   as Module
import qualified Data.List                    as List
import qualified Data.HashMap.Strict                     as Map
import qualified Data.Map as NormalMap
import qualified Data.Set                     as Set
import           Elm.Compiler.Module
import           Optimize.Traversals

import qualified AST.Variable                 as Variable

import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.Types

import qualified AST.Variable                 as Var

import           Optimize.ControlFlow
import           Optimize.EmbellishedMonotone
import           Optimize.RelevantDefs
import Data.Hashable

import qualified Data.HashSet as HSet

--import Optimize.Reachability (reachabilityMap)

import           Debug.Trace                  (trace)
--trace _ x = x


-- | How long do we allow our call strings to get?
contextDepth = 2

-- | Nodes in our system dependence graph
-- | A node is either a program point, a program point that defines a value,
-- | Or a special node corresponding to function call/return or entry/exit
data SDGNode = SDGDef VarPlus Label | SDGLabel Label | SDGFunction LabelNode
  deriving (Eq, Ord, Show)

instance Hashable SDGNode where
  hashWithSalt _ n = case n of
    SDGDef _ l -> l
    SDGLabel l -> l
    SDGFunction ln -> getNodeLabel ln

-- | The payload of our monotone analysis: the sets of SDG nodes
-- | Reachable by each given SDG node
-- | An edge here represents influence
-- | So if B is dependent on A, (A,B) is an edge in our graph
newtype SDG = SDG {unSDG :: Set.Set SDGNode}
  deriving (Eq, Ord, Show)

-- | Convert our "target" i.e. epxported label node functions into SDG nodes
makeTargetSet :: Set.Set LabelNode -> Set.Set SDGNode
makeTargetSet = Set.map toSDG

-- | Convert a Label node into an SDG node
--TODO function case?
toSDG :: LabelNode -> SDGNode
toSDG lnode = case lnode of
  Assign var label -> SDGDef var label
  Call _ -> SDGFunction lnode
  Return _ _ -> SDGFunction lnode
  ProcEntry _ -> SDGFunction lnode
  ProcExit _ -> SDGFunction lnode
  _ -> SDGLabel $ getNodeLabel lnode

-- | The lattice corresponding to forward slicing
-- | Join is just union
-- | Our extremal value is the set of "target" nodes, since they are always reachable
-- | Our analysis is backwards: If B reaches A, and (C,B) is an SDG edge, then C reaches A
-- | So information flows backwards along SDG edges
forwardSliceLattice :: Set.Set SDGNode -> Lattice SDG
forwardSliceLattice startDefs = Lattice {
  --latticeTop :: a
  latticeBottom = SDG Set.empty ,
  latticeJoin = \(SDG s1) (SDG s2) -> SDG $ Set.union s1 s2,
  iota = SDG startDefs, --Extremal value for our analysis
  lleq = \(SDG s1) (SDG s2) -> s1 `Set.isSubsetOf` s2,
  flowDirection = BackwardAnalysis
  }

-- | The embellished version of our forward-slice lattice
embForwardSliceLat domain startDefs  =
  liftToEmbellished domain (SDG startDefs) (forwardSliceLattice startDefs)

-- |Our transfer funciton is basically the identity,
-- |With the necessary lifting dealing with function return and call
transferFun
  :: Lattice SDG
  -> Map.HashMap SDGNode (EmbPayload SDGNode SDG)
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
      (EmbPayload (domain2, lcall)) = trace "Map1" $ resultDict Map.! (SDGFunction $ Call l)
    in EmbPayload (domain,  \d ->
     (lcall d) `latticeJoin` (pl ((SDGFunction $ Call l):d) ) )
  _ -> lhat

transferFun Lattice{..} resultDict lnode lhat@(EmbPayload (domain, pl)) = lhat

-- | Determines if a CFG edge is for a special function call/return action
--to go in our call-graph
isFunctionEdge :: (LabelNode, LabelNode) -> Bool
isFunctionEdge edge = case edge of
  (Call _, ProcEntry _ ) -> True
  (ProcExit _, Return _ _ ) -> True
  _ -> False

-- | Given a CFG edge, make an SDG edge for the special function action of the edge
makeFunctionEdge :: (LabelNode, LabelNode) -> (SDGNode, SDGNode)
makeFunctionEdge (n1, n2) = (SDGFunction n1, SDGFunction n2)

{-| Given function info about imported functions,
the names of functions this module exports, and the expression for this module,
return the ProgramInfo of its SDG, and the list of extremal SDG nodes
for the exported functions
|-}
sdgProgInfo
  :: NormalMap.Map Var FunctionInfo
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
            (\n rdSet -> [(SDGDef var def, toSDG n) | (var,  def) <- (HSet.toList rdSet)] ) relevantDefs
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

-- | Use function application to get the reached set from an embellished-lattice value
--TODO all?
--setFromEmb :: EmbPayload SDGNode SDG -> Set.Set SDGNode
{-
setFromEmb startDefs (EmbPayload (domain, lhat)) =
  unSDG $ joinAll normalLat $ map (lhat $) domain
    where normalLat = forwardSliceLattice startDefs
-}

{-|
Given info about imported functions,
the list of names this module exports,
and the canonical expression for this module,
return the module with its unused definitions removed.
|-}
removeDeadCode
  :: NormalMap.Map Var FunctionInfo
    -> [Name]
    -> Canon.Expr
    -> Canon.Expr
removeDeadCode initFnInfo targetVars e = case dependencyMap of
  Nothing -> trace "!!! Couldn't Optimize" e
  Just (depMap, targetNodes) -> trace "Opt Success" $ toCanonical
       $ removeDefs targetNodes depMap eAnn
    -- $ removeDefs (toDefSet depMap targetNodes) eAnn --TODO
  where
    eAnn = annotateCanonical (NormalMap.empty)  (startLabel) e
    dependencyMap = do
      (pinfo, targetNodes) <- sdgProgInfo initFnInfo targetVars eAnn
      let reachMap = callGraph eAnn
      let fnLabels = (Map.keys reachMap)
      let domain = map (\d -> map (\l -> SDGFunction (Call l)) d ) $ contextDomain fnLabels contextDepth reachMap
      let (_,embDefMap) =
            minFP --(forwardSliceLattice (Set.fromList targetNodes)) (\_ _ x -> x ) pinfo
              (embForwardSliceLat
                 (domain) $ Set.fromList targetNodes)
               (transferFun $ forwardSliceLattice $ Set.fromList targetNodes) pinfo
      let applyContext (EmbPayload (domain, lhat)) =
            joinAll (forwardSliceLattice (Set.fromList targetNodes)) $ map (lhat $ ) domain
      let defMap = Map.map applyContext embDefMap
      return $  (defMap, targetNodes)

-- |Given a set of target nodes, a map from nodes to other nodes depending on that node,
-- | And a module's expression, traverse the tree and remove unnecessary Let definitions
removeDefs
  :: [Optimize.SDG.SDGNode]
  -> Map.HashMap SDGNode SDG
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

{-|
Remove monadic assignment statements from a monadic function,
if they don't influence the final return value
|-}
removeDefsMonadic
  :: [Optimize.SDG.SDGNode]
  -> Map.HashMap SDGNode SDG
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
            then (monadRemoveStatements
                    targetNodes depMap (functionArgsAndAnn body) (functionBody body ))
            else body
        in GenericDef pat newBody ty) defList

-- | Get the annotation for a given function
getAnn (A a _) = a

-- | Given a  list of target nodes,
-- | a mapping of nodes to nodes they are relevant to (result of our FP iteration)
-- | and the body of a monadic function
-- | Return that monadic function with irrelevant statements removed
monadRemoveStatements
  :: [SDGNode]
  -> Map.HashMap SDGNode SDG
  -> [(Pattern, (Region, Label, Env Label))]
  -> LabeledExpr
  -> LabeledExpr
monadRemoveStatements  targetNodes reachedNodesMap argPatLabels monadBody = trace "!!!MonadRemove"$
  let
    op = Var.Canonical (Var.Module ["State", "Escapable"] ) ("andThen")
    taskStructure = sequenceMonadic monadBody
    --patLabels = map snd patStatements
    --allStatements = (map fst patStatements) ++ [lastStmt]

    cleanMonadic taskStruct = trace "Clean monadic" $ case taskStruct of
      TSeq expr s1 pat s2 -> if (isRelevantStmt  s1 )
                            then TSeq expr (cleanMonadic s1) pat (cleanMonadic s2)
                            else (cleanMonadic s2)
      TCase expr e cases -> TCase expr e $ map (\(p,s) -> (p, cleanMonadic s)) cases
      TBranch expr guardCases -> TBranch expr $ map (\(g,s) -> (g, cleanMonadic s)) guardCases
      _ -> taskStruct

    
    isRelevantStmt t = trace "Is Relevant?" $ case t of
      Task s -> trace ("Is rel stmt? " ++ show ( writeIsRelevant  (getLabel s) ) ) $ writeIsRelevant  (getLabel s)
      TSeq exp s1 pat s2  -> trace ("Is rel result? " ++ show (resultIsRelevant pat (getLabel exp) )) $  (resultIsRelevant pat (getLabel exp) ) ||
        (isRelevantStmt  s1) || (isRelevantStmt s2)
      TCase expr e cases -> trace "TCase rel" $ or $ map (isRelevantStmt ) $ map snd cases
      TBranch expr cases -> trace "IfCase rel" $ or $ map (isRelevantStmt ) $ map snd cases
      TCall _ expr -> trace "Call rel" $ True --TODO more fine grained? 
      

    writeIsRelevant  label =
      let
          --TODO check, is this right? Why don't we look at pattern?
           --definedVars =  getPatternVars `fmap` maybePat
           --patAssigns =[SDGDef (NormalVar var label) label | var <- definedVars]
           ourAssigns =  
             [(SDGDef var compLab) |
                                     (SDGDef var compLab)<-Map.keys reachedNodesMap,
                                     compLab == label]
           --ourAssigns = [(SDGDef var compLab) |
           --                          (SDGDef var compLab)<-Map.keys reachedNodesMap,
           --                          compLab == getLabel stmt]--TODO make faster
           reachedNodes = Set.unions $ map
             (\varNode -> case (reachedNodesMap Map.! varNode) of
                    x -> unSDG x) ourAssigns
           isRel = not $ Set.null $ (Set.fromList targetNodes) `Set.intersection` reachedNodes
       in  trace ("Write relevant? " ++ show isRel ++ " " ++ show label  ++ "\nSets " ++ show reachedNodes ) $ isRel

    resultIsRelevant pat label =
      let
          --TODO check, is this right? Why don't we look at pattern?
           definedVars =  getPatternVars pat
           --patAssigns =[SDGDef (NormalVar var label) label | var <- definedVars]
           ourAssigns = [SDGDef (NormalVar var label) label | var <- definedVars]
           --ourAssigns = [(SDGDef var compLab) |
           --                          (SDGDef var compLab)<-Map.keys reachedNodesMap,
           --                          compLab == getLabel stmt]--TODO make faster
           reachedNodes = Set.unions $ map
             (\varNode -> case (reachedNodesMap Map.! varNode) of
                    x -> unSDG x) ourAssigns
           isRel = not $ Set.null $ (Set.fromList targetNodes) `Set.intersection` reachedNodes
       in  trace ("Result relevant? " ++ show isRel ++ " " ++ show label ++ " " ++ show pat ++ "\nSets " ++ show reachedNodes ) $ isRel
           
    cleanedStmt = cleanMonadic taskStructure
    --Put our monadic statements back into functional form
    reAssembleSeq :: TaskStructure -> LabeledExpr
    reAssembleSeq t = case t of
      (TSeq expr stmt pat rest) ->
         (A (getAnn expr) $ Binop op (reAssembleSeq stmt) (A (getAnn $ reAssembleSeq rest)
                           $ Lambda pat $ reAssembleSeq rest))
      (TBranch expr guardCases) ->
         A (getAnn expr) $ MultiIf $
           map (\(g,s) -> (g, reAssembleSeq s)) guardCases
      (TCase expr caseExp patSeqPairs) ->
        A (getAnn expr) $ Case caseExp $ map (\(p,s) -> (p, reAssembleSeq s)) patSeqPairs
      (Task s) -> s
      (TCall _ s) -> s
    
    --Add our function arguments back
    reAssemble [] accum = accum
    reAssemble ((argPat, ann):rest) accum = reAssemble rest $ A ann (Lambda argPat accum) 
  in reAssemble (reverse argPatLabels) $ reAssembleSeq cleanedStmt


-- | Given the label for the RHS of a definition,
-- | a list of target nodes,
-- | a mapping of nodes to nodes they are relevant to (result of our FP iteration)
-- | and a Definition, return true if we should keep the definition
defIsRelevant :: Label -> [SDGNode] -> Map.HashMap SDGNode SDG -> LabelDef -> Bool
defIsRelevant defLabel targetNodes reachedNodesMap (GenericDef pat expr _ty) = let
        definedVars = getPatternVars pat
        definedVarPlusses = map (\v -> NormalVar v defLabel) definedVars
        --nodesForDefs = map (\var -> SDGDef var (getLabel expr)) definedVarPlusses
        --Get labels in the same way we do for defs in CFG
        nodesForDefs = map toSDG $ map (getLabel `fmap`) $ varAssign pat expr
        reachedNodes = Set.unions $
          map (\varNode -> case (Map.lookup varNode reachedNodesMap ) of
                  Just x -> unSDG x
                  Nothing -> Set.empty) nodesForDefs
                  -- EmbPayload _ lhat -> unSDG $ lhat []) nodesForDefs
        isRel = not $ Set.null $ (Set.fromList targetNodes) `Set.intersection` reachedNodes
      in trace ("Testing if " ++ show pat ++ " is relevant\n" ++ (show $ Set.fromList targetNodes) ++ "\n" ++ show reachedNodes ++ ("Nodes for def " ++ show definedVars ++ " : " ++ show nodesForDefs) ) $ isRel



-- | Given interfaces of imported modules, a module and its interface
-- | Perform dead code elimination on that module
removeModuleDeadCode :: ModuleOptFun
removeModuleDeadCode otherIfaces modName  (modul, iface) = trace (show modName) $ let
    fnInfo = interfaceFnInfo otherIfaces
    isValue value = case value of --TODO remove
      Variable.Value s -> True
      _ -> False
    valToName (Variable.Value s) = Name [s]
    names = map valToName $ filter isValue $ Module.iExports iface
  in (tformModule (removeDeadCode fnInfo names) modul, iface)
