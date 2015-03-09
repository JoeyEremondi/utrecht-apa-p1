{-# LANGUAGE DeriveFunctor #-}
module Optimize.RelevantDefs (getRelevantDefs) where

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


import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.EmbellishedMonotone
import           Optimize.Types

import Optimize.ControlFlow

insertAll :: Ord k => [(k,a)] -> Map.Map k a -> Map.Map k a
insertAll pairs theMap = foldr (\(k,a) m -> Map.insert k a m) theMap pairs  





    


--Give the list of definitions  
getRelevantDefs
  :: [Name]
  -> Canon.Expr
  -> Maybe (Map.Map Label (Set.Set (Name, Label)))
getRelevantDefs targets e =
  let
    eAnn = annotateCanonical (error "TODO initial global env")  (Label []) e
    initalEnv = globalEnv eAnn
    (A _ (Let defs _)) = eAnn
    fnInfo =
      foldr (\(GenericDef (Pattern.Var n) body _ ) finfo ->
              Map.insert (error "TODO name to var")
              (FunctionInfo
               (getArity body)
               (map (\pat -> FormalParam pat (getLabel body) ) (functionArgPats body)) 
               (ProcEntry eAnn)
               (ProcExit eAnn)
              ) finfo) Map.empty defs
    edgeListList = forM defs (\(GenericDef _ expr _) -> allExprEdges fnInfo expr)
    edges = concat `fmap` edgeListList
    progInfo = makeProgramInfo `fmap` edges
  in case progInfo of
    Nothing -> Nothing
    _ -> return Map.empty


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
reachingDefs :: Set.Set RDef -> Lattice ReachingDefs
reachingDefs iotaVal =  Lattice {
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
transferFun :: Map.Map Label LabeledExpr -> LabelNode -> ReachingDefs -> ReachingDefs
transferFun labMap cfgNode (ReachingDefs aIn) =
  ReachingDefs $ (removeKills cfgNode aIn) `Set.union` (gens cfgNode)


genericDefVars :: GenericDef a Var -> [Var]
genericDefVars (GenericDef p _ _) = getPatternVars p
