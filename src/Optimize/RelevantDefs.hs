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

insertAll :: Ord k => [(k,a)] -> Map.Map k a -> Map.Map k a
insertAll pairs theMap = foldr (\(k,a) m -> Map.insert k a m) theMap pairs  

--Type for variables or some "special cases"
data VarPlus =
  NormalVar [Var]
  | IntermedExpr Label
  | FormalReturn Var
  | ActualParam Label
  | FormalParam Pattern Label
    deriving (Eq, Ord)
--TODO how to make sure all our IntermedExprs are there?

--Our different types of control nodes
data ControlNode' expr =
  Branch (expr)
  | Assign VarPlus (expr)
  -- | AssignParam (expr)
  | Call (expr) 
  | Return Var (expr) --TODO assign to what?
  | ProcEntry (expr)
  | ProcExit (expr)
  | GlobalEntry --Always the first node
  | GlobalExit --Always the last node
    deriving (Functor, Eq, Ord)


type ControlNode = ControlNode' LabeledExpr
type LabelNode = ControlNode' Label

type ControlEdge = (ControlNode, ControlNode)

getLabel :: LabeledExpr -> Label
getLabel (A (_,l,_) _) = l

--For a fuction parameter, we treat each tail-position expression in the parameter
--As an assignment to the actual value of that parameter
paramNodes :: [LabeledExpr] -> [[ControlNode]]
paramNodes = map (\ arg ->
                         map (\tailExpr ->
                           Assign (ActualParam $ getLabel arg) tailExpr ) $ tailExprs arg)


tailExprs :: LabeledExpr -> [LabeledExpr]
tailExprs wholeExp@(A _ e) = tailExprs' e
  where
    tailExprs' (MultiIf guardBodies) = concatMap tailExprs $ map snd guardBodies
    tailExprs' (Case e cases) = concatMap tailExprs $ map snd cases
    tailExprs' (Let defs body) = tailExprs body
    tailExprs' e = [wholeExp] --All other cases, the expression itself is the returned value, no control flow

tailAssign :: Label ->  LabeledExpr -> ControlNode
tailAssign label tailExpr = Assign (IntermedExpr label) tailExpr

binOpToFn :: LabeledExpr -> LabeledExpr
binOpToFn (A ann (Binop op _ _)) = A ann $ Var op

connectLists :: ([ControlNode], [ControlNode]) -> [ControlEdge]
connectLists (l1, l2) = [(n1, n2) | n1 <- l1, n2 <- l2]

data FunctionInfo =
  FunctionInfo
  {
    arity :: Int,
    formalParams :: [VarPlus],
    entryNode :: ControlNode,
    exitNode :: ControlNode
  }

    

--Used in a foldE to generate statements/control nodes for expressions that need one
--Later we'll go in and add control edges
oneLevelEdges
  :: Map.Map Var FunctionInfo
  -> LabeledExpr
  -> [Maybe (
     Map.Map Label [ControlNode]
    ,Map.Map Label [ControlNode]--Entry and exit node for sub exps
    --,[ControlNode]
    ,[ControlEdge]) ]
  -> Maybe (
     Map.Map Label [ControlNode]
    ,Map.Map Label [ControlNode]--Entry and exit node for sub exps
    --,[ControlNode]
    ,[ControlEdge])
oneLevelEdges fnInfo e@(A (_, label, env) expr) maybeSubInfo = do
  (headMaps, tailMaps, {-subNodesL,-} subEdgesL) <- List.unzip3 `fmap` mapM id maybeSubInfo --Edges and nodes from our sub-expressions
  --let subNodes = concat subNodesL
  let headMap = Map.unions headMaps
  let tailMap = Map.unions tailMaps
  let subEdges = concat subEdgesL
  case expr of
    --Function: we have call and return for the call, and evaluating each arg is a mock assignment
    App e1 e2 -> do
      fnName <- functionName e1
      argList <- argsGiven e1
      let numArgs = length argList
      thisFunInfo <- Map.lookup fnName fnInfo 
      let fnArity = arity thisFunInfo
      let inLocalScope = Map.member fnName env
      let argNodes = paramNodes argList
      let callNode = Call e
      let retNode = Return fnName e
      --Generate assignment nodes for the actual parameters to the formals
      let assignFormalNodes =
            map (\(formal, arg) -> Assign formal arg) $ zip (formalParams thisFunInfo) argList
      --Control edges to generate
      let firstHead = (headMap Map.! (getLabel $ head argList))
      let otherHeads = map (\arg -> headMap Map.! (getLabel $ arg) ) $ tail argList
      let tailLists = map (\arg -> tailMap Map.! (getLabel $ arg) )  argList
      --let (otherTails, lastTail) = (init tailLists, last tailLists)
      let assignParamEdges = concatMap connectLists $ zip tailLists argNodes
      let calcNextParamEdges = concatMap connectLists $ zip (init argNodes) otherHeads
      let gotoFormalEdges = connectLists ((last argNodes), [head assignFormalNodes])

      let assignFormalEdges = zip (init assignFormalNodes) (tail assignFormalNodes)
      let callEdges = [(last assignFormalNodes, callNode ),
                      (callNode, entryNode thisFunInfo)]
      let returnEdges =
            [ (exitNode thisFunInfo, retNode)
            ]
      
      --TODO add edges to function entry, assigning formals
      --TODO check for shadowing?
      case (fnArity == numArgs, inLocalScope) of
        (True, False) -> return $
                        (Map.insert (getLabel e) firstHead headMap,
                         Map.insert (getLabel e) [retNode] tailMap,
                          --[callNode, retNode] ++ (concat argNodes),
                         assignParamEdges ++ calcNextParamEdges ++
                           gotoFormalEdges ++ callEdges ++
                           callEdges ++ returnEdges ++ subEdges ) --TODO app edges
          
        _ -> Nothing --If function is locally defined, or not fully instantiated, we fail
    Lambda _ _ -> Nothing --Fail for local lambda defs --TODO lambda case?
    Binop op e1 e2 -> case (error "TODO check if arith") of
      True -> return (Map.insert (getLabel e) (headMap Map.! (getLabel e1)) headMap  
                        , Map.insert (getLabel e) (tailMap Map.! (getLabel e2)) headMap
                          ,subEdges ) --Arithmetic doesn't need its own statements, since we can do inline
      False -> oneLevelEdges fnInfo (binOpToFn e) maybeSubInfo
    --Data _ args -> paramNodes args --Ctor is a constant, so just evaluate the arguments
    MultiIf condCasePairs -> do
      --We treat each case of the if expression as an assignment to the final value
      --of the if expression
      let guards = (map fst condCasePairs) 
      let bodies = map snd condCasePairs
      let bodyTails = concatMap tailExprs bodies
      let guardNodes = map Branch guards
      let bodyNodes = map (tailAssign $ getLabel e) bodyTails
      --Each guard is connected to the next guard, and the "head" control node of its body
      let ourHead = headMap Map.! (getLabel $ head guards)
      let otherHeads = map (\arg -> headMap Map.! (getLabel $ arg) ) (tail guards)
      let guardEnds = map (\arg -> tailMap Map.! (getLabel $ arg) ) guards
      let notLastGuardEnds = init guardEnds
      let bodyHeads = map (\arg -> headMap Map.! (getLabel $ arg) ) bodies

      let guardFallthroughEdges = concatMap connectLists $ zip notLastGuardEnds otherHeads
      let guardBodyEdges = concatMap connectLists $ zip guardEnds bodyHeads 
      
      return (
        Map.insert (getLabel e) ourHead headMap --First statement is eval first guard
         ,Map.insert (getLabel e) bodyNodes tailMap --Last statements are any tail exps of bodies
        --,guardNodes ++ bodyNodes ++ subNodes
         ,subEdges ++ guardBodyEdges ++ guardFallthroughEdges)
    Case caseExpr patCasePairs -> do
      --We treat each case of the case expression as an assignment to the final value
      --of the case expression
      --Those assignments correspond to the expressions in tail-position of the case
      let cases = map snd patCasePairs
      let caseNodes = map (\tailExpr -> Assign (IntermedExpr $ getLabel e) tailExpr) cases
      let branchNode = Branch e
      let ourHead = case (headMap Map.! (getLabel caseExpr)) of
            [] -> [Assign (IntermedExpr $ getLabel caseExpr) caseExpr]
            headList -> headList
      let caseHeads = concatMap (\cs -> headMap Map.! (getLabel cs) ) cases
      let branchEdges = connectLists (ourHead, [branchNode])
      let caseEdges =  connectLists ([branchNode], caseHeads)
      return $ (Map.insert (getLabel e) ourHead headMap
        ,Map.insert (getLabel e) caseNodes tailMap --Last thing is tail statement of whichever case we take
        --,[Assign (IntermedExpr $ getLabel caseExpr) caseExpr] ++ caseNodes ++ subNodes
         ,subEdges ++ caseEdges)
    Let defs body -> do
      --We treat the body of a let statement as an assignment to the final value of
      --the let statement
      --Those assignments correspond to the expressions in tail-position of the body
      let orderedDefs = defs --TODO sort these
      let getDefAssigns (GenericDef pat b _) = map (varAssign pat) $ tailExprs b
      let defAssigns = map getDefAssigns orderedDefs
      --let bodyAssigns = map (tailAssign $ getLabel e) $ tailExprs body

      let allHeads = map (\(GenericDef _ b _) -> headMap Map.! (getLabel b)) orderedDefs
      
      let ourHead = case (head allHeads) of
            [] -> head defAssigns
            headList -> headList
      let otherHeads = tail allHeads
      --TODO separate variables?

      let bodyHead = headMap Map.! (getLabel body)
      let tailLists = map (tailMap Map.!) $map (\(GenericDef _ b _) -> getLabel b) orderedDefs
      
      
      let betweenDefEdges =
            concatMap connectLists $ zip defAssigns (otherHeads ++ [bodyHead])
      let tailToDefEdges = concatMap connectLists $ zip tailLists defAssigns
      --TODO need intermediate?
      
      return $ (Map.insert (getLabel e) ourHead headMap
                ,Map.insert (getLabel e) (tailMap Map.! (getLabel body)) tailMap
                --,defAssigns ++ bodyAssigns ++ subNodes
                ,subEdges ++ betweenDefEdges ++ tailToDefEdges)
        
    _ -> case (headMaps) of
      [] -> return (Map.empty, Map.empty,  subEdges) --Means we are a leaf node, no sub-expressions
      _ -> do
        let headLists = Map.elems headMap
        let tailLists = Map.elems tailMap
        let (ourHead:otherHeads) = headLists
        let otherTails = init tailLists
        let ourTail = last tailLists
        let subExpEdges = concatMap connectLists $ zip otherTails otherHeads
        return (Map.insert (getLabel e) ourHead headMap
              , Map.insert (getLabel e) ourTail tailMap
               --, subNodes
               , subEdges ++ subExpEdges)
        --Other cases don't generate control nodes for one-level analysis
        --For control flow, we just calculate each sub-expression in sequence
        --We connect the end nodes of each sub-expression to the first of the next
   
varAssign :: Pattern -> LabeledExpr -> ControlNode
varAssign pat e = Assign (NormalVar $ getPatternVars pat) e


functionName :: LabeledExpr -> Maybe Var
functionName (A _ e) = case e of
  Var v -> Just v
  (App f _ ) -> functionName f
  _ -> Nothing

functionBody :: LabeledExpr -> LabeledExpr
functionBody (A _ (Lambda _ e)) = functionBody e
functionBody e = e

functionArgPats :: LabeledExpr -> [Pattern]
functionArgPats (A _ (Lambda pat e)) = [pat] ++ (functionArgPats e)
functionArgPats _ = []

getArity :: LabeledExpr -> Int
getArity (A _ (Lambda _ e)) = 1 + (getArity e)
getArity e = 0

argsGiven :: LabeledExpr -> Maybe [LabeledExpr]
argsGiven (A _ e) = case e of
  Var v -> Just []
  (App f e ) -> ([e]++) `fmap` argsGiven f
  _ -> Nothing



allExprEdges
  :: Map.Map Var FunctionInfo
  -> LabeledExpr
  -> Maybe [(ControlNode, ControlNode)]
allExprEdges fnInfo e = (\(_,_,edges) -> edges) `fmap` foldE
           (\ _ () -> repeat ())
           ()
           (\(GenericDef _ e v) -> [e])
           (\ _ e subs-> oneLevelEdges fnInfo e subs)
           e

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
