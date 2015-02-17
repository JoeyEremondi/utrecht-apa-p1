{-# LANGUAGE DeriveFunctor #-}
module Optimize.ForwardSlicing (removeDeadCodeWP, removeDeadCodeModule) where

import Elm.Compiler.Module
import qualified Data.Map as Map
import Optimize.Traversals
import qualified AST.Module as Module
import qualified AST.Pattern as Pattern
import qualified AST.Expression.Canonical as Canon
import AST.Annotation (Annotated(..))
import AST.Expression.General
import Control.Monad
import qualified Data.List as List


import Optimize.Types
import Optimize.Environment
import Optimize.MonotoneFramework

--Our different types of control nodes
data ControlNode' expr =
  Start (expr)
  | End (expr)
  | Call (expr)
  | Return (expr)
  | ProcEntry (expr)
  | ProcExit (expr)
  | GlobalEntry --Always the first node
  | GlobalExit --Always the last node
    deriving (Functor, Eq, Ord)

type ControlNode = ControlNode' LabeledExpr
type LabelNode = ControlNode' Label

type ControlEdge = (ControlNode, ControlNode)

functionName :: LabeledExpr -> Maybe Var
functionName (A _ e) = case e of
  Var v -> Just v
  (App f _ ) -> functionName f
  _ -> Nothing

functionBody :: LabeledExpr -> LabeledExpr
functionBody (A _ (Lambda _ e)) = functionBody e
functionBody e = e

getArity :: LabeledExpr -> Int
getArity (A _ (Lambda _ e)) = 1 + (getArity e)
getArity e = 0

argsGiven :: LabeledExpr -> Maybe [LabeledExpr]
argsGiven (A _ e) = case e of
  Var v -> Just []
  (App f e ) -> ([e]++) `fmap` argsGiven f
  _ -> Nothing
  
--Generate control-flow edges for a single expression
--We then pass this function to a fold, which collects them
oneLevelEdges
  :: Map.Map Var Int
  -> Map.Map Var (ControlNode, ControlNode) --Map of entry and exit nodes
  -> LabeledExpr
  -> Maybe [ControlEdge]
oneLevelEdges aritys fnNodes e@(A (_,_,env) e') =
  case e' of
    (Range e1 e2) -> return [(Start e, Start e1), (End e1, Start e2), (End e2, End e)]
    (ExplicitList l) ->
      let
        startList = [Start e] ++ map Start l
        endList = (map End l) ++ [End e]
      in return $ zip startList endList
    (Binop op e1 e2) -> return [(Start e, Start e1), (End e1, Start e2), (End e2, End e)]
    (Lambda e1 e2) -> Nothing --TODO handle this case? Initial level?
    (App e1 e2) -> do
      fnName <- functionName e1
      argList <- argsGiven e1
      let numArgs = length argList
      arity <- Map.lookup fnName aritys
      let inLocalScope = Map.member fnName env
      --TODO check for shadowing?
      case (arity == numArgs, inLocalScope) of
        (True, False) -> do
          (pentry, pexit) <- Map.lookup fnName fnNodes
          let starts = [Start e] ++ map Start argList
          let ends = (map End argList) ++ [Call e]
          return $ [(Call e, pentry), (pexit, Return e)] ++ (zip starts ends)
        _ -> Nothing --If function is locally defined, or not fully instantiated, we fail
    (MultiIf guardCasePairs) ->
      let
        guards = map fst guardCasePairs
        starts = [Start e] ++ (map Start guards)
        ends = (map End guards) ++ [End e] --TODO go to failure case?
        innerEdges = concatMap (\(g, c) -> [(End g, Start c), (End c, End e)]) guardCasePairs
        --TODO does flow go from each guard to next, or from whole to each guard
      in return $ innerEdges ++ (zip starts ends)
    (Let e1 e2) -> error "TODO implement cases for let expressions"
    (Case e1 cases) -> return $ 
      [(Start e, Start e1)] ++
      concatMap (\(_pat, e2) -> [(End e1, Start e2), (End e2, Start e)]) cases
    (Data ctor args) -> let
        startList = [Start e] ++ map Start args
        endList = (map End args) ++ [End e]
      in return $ zip startList endList
    (Access e1 _) -> return $ [(Start e, Start e1), (End e1, End e)]
    (Remove e1 _) -> return $ [(Start e, Start e1), (End e1, End e)]
    (Insert e1 _ e2) -> return $ [(Start e, Start e1), (End e1, Start e2), (End e2, End e)]
    (Modify e1 newVals) ->
      let
        exprs = map snd newVals
        starts = [Start e] ++ map Start exprs
        ends = (map End exprs) ++ [End e]
        
      in return $ zip starts ends
    (Record nameExprs) ->
      let
        exprs = map snd nameExprs
        starts = [Start e] ++ map Start exprs
        ends = (map End exprs) ++ [End e]
      in return $ zip starts ends
    (PortIn e1 e2) -> return []
    (PortOut _ _ e1) -> return $ [(Start e, Start e1), (End e1, End e)]
    (GLShader _ _ _ ) -> return []

allExprEdges
  :: Map.Map Var Int
  -> Map.Map Var (ControlNode, ControlNode)
  -> LabeledExpr
  -> Maybe [(ControlNode, ControlNode)]
allExprEdges aritys fnNodes = foldE
           (\ _ () -> repeat ())
           ()
           (\(GenericDef _ e v) -> [e])
           (\ _ e maybeSubs -> do
               thisLevel <- oneLevelEdges aritys fnNodes e
               subEdges <- sequence maybeSubs
               return $ thisLevel ++ (concat subEdges))



removeDeadCodeWP :: [Name] 
  -> Map.Map Name (Module, Interface)
  -> Map.Map Name (Module, Interface) 
removeDeadCodeWP _ m = m --TODO implement


removeDeadCodeModule :: Name -> (Module, Interface) -> (Module, Interface)
removeDeadCodeModule n (m,i) =
  let
    newMod = tformModule removeDeadCode m
  in (newMod,i)

removeDeadCode :: Canon.Expr -> Canon.Expr
removeDeadCode e =
  let
    eAnn = annotateCanonical (error "TODO initial global env")  (Label []) e
    initalEnv = globalEnv eAnn
    (A _ (Let defs _)) = eAnn
    (aritys, fnNodes) =
      foldr (\def (ae, fe) ->
              case def of
                (GenericDef (Pattern.Var n) body _ ) ->
                  (Map.insert (error "TODO make name to var") (getArity body) ae,
                   Map.insert (error "TODO make name to var") (ProcEntry body, ProcExit body) fe))
                --_ -> (ae, fe)  --TODO what is this case?
      (Map.empty, Map.empty) defs
    edgeListList = forM defs (\(GenericDef _ expr _) -> allExprEdges aritys fnNodes expr)
    edges = concat `fmap` edgeListList
    progInfo = makeProgramInfo `fmap` edges
  in case progInfo of
    Nothing -> e
    _ -> e--TODO implement

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
