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

--Type for variables or some "special cases"
data VarPlus =
  NormalVar [Var]
  | IntermedExpr Label
  | ReturnVal Label
  | ActualParam Label
  | FormalParam Label
    deriving (Eq, Ord)

--Our different types of control nodes
data ControlNode' expr =
  Branch (expr)
  | Assign VarPlus (expr)
  -- | AssignParam (expr)
  | Call (expr) 
  | Return (expr) --TODO assign to what?
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
paramNodes :: [LabeledExpr] -> [ControlNode]
paramNodes = concatMap (\ arg ->
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

binOpToFn :: Var -> LabeledExpr
binOpToFn = _

--Used in a foldE to generate statements/control nodes for expressions that need one
--Later we'll go in and add control edges
toControlNode
  ::Map.Map Var Int
  -> LabeledExpr
  -> [Maybe (
     [ControlNode]
    ,[ControlNode]--Entry and exit node for sub exps
    ,[ControlNode]
    ,[ControlEdge]) ]
  -> Maybe (
     [ControlNode]
    ,[ControlNode]--Entry and exit node for sub exps
    ,[ControlNode]
    ,[ControlEdge])
toControlNode arities e@(A (_, label, env) expr) maybeSubInfo = do
  (headLists, tailLists, subNodesL, subEdgesL) <- List.unzip4 `fmap` mapM id maybeSubInfo --Edges and nodes from our sub-expressions
  let subNodes = concat subNodesL
  let subEdges = concat subEdgesL
  case expr of
    --Function: we have call and return for the call, and evaluating each arg is a mock assignment
    App e1 e2 -> do
      fnName <- functionName e1
      argList <- argsGiven e1
      let numArgs = length argList
      arity <- Map.lookup fnName arities
      let inLocalScope = Map.member fnName env
      let argNodes = paramNodes argList
      let retNode = return e
      --TODO check for shadowing?
      case (arity == numArgs, inLocalScope) of
        (True, False) -> return $
                        ([head argNodes],
                         [Return e],
                          [Call e, Return e] ++ argNodes,
                         [] ) --TODO app edges
          
        _ -> Nothing --If function is locally defined, or not fully instantiated, we fail
    Lambda _ _ -> Nothing --Fail for local lambda defs
    Binop op e1 e2 -> case (error "TODO check if arith") of
      True -> return (head headLists, last tailLists, subNodes, subEdges ) --Arithmetic doesn't need its own statements, since we can do inline
      False -> do
        let retNode = Return (binOpToFn op)
        let argNodes = paramNodes [e1, e2]
        return ([head argNodes],
                [retNode],
                [Call (binOpToFn op), retNode] ++ argNodes ++ subNodes,
                subEdges) --TODO app edges
    --Data _ args -> paramNodes args --Ctor is a constant, so just evaluate the arguments
    MultiIf condCasePairs -> do
      --We treat each case of the if expression as an assignment to the final value
      --of the if expression
      let guards = (map fst condCasePairs) 
      let bodies = map snd condCasePairs
      let bodyTails = concatMap tailExprs bodies
      let guardNodes = paramNodes guards
      let bodyNodes = map (tailAssign $ getLabel e) bodyTails
      --Each guard is connected to the next guard, and the "head" control node of its body
      
      return $ (
        [head guardNodes]--First statement is eval first guard
         ,bodyNodes --Last statements are any tail exps of bodies
        ,guardNodes ++ bodyNodes ++ subNodes
         ,subEdges)
    Case caseExpr patCasePairs -> do
      --We treat each case of the case expression as an assignment to the final value
      --of the case expression
      --Those assignments correspond to the expressions in tail-position of the case
      let cases = map snd patCasePairs
      let caseNodes = map (\tailExpr -> Assign (IntermedExpr $ getLabel e) tailExpr) cases
      let ourHeads = case (head headLists) of
            [] -> [Assign (IntermedExpr $ getLabel caseExpr) caseExpr]
            headList -> headList
      return $ (ourHeads --First thing we do is compute the expr we switch on
        ,caseNodes --Last thing is tail statement of whichever case we take
        ,[Assign (IntermedExpr $ getLabel caseExpr) caseExpr] ++ caseNodes ++ subNodes
         ,subEdges)
    Let defs body -> do
      --We treat the body of a let statement as an assignment to the final value of
      --the let statement
      --Those assignments correspond to the expressions in tail-position of the body
      let orderedDefs = defs --TODO sort these
      let getDefAssigns (GenericDef pat body _) = map (varAssign pat) $ tailExprs body
      let defAssigns = concatMap getDefAssigns orderedDefs
      let bodyAssigns = map (tailAssign $ getLabel e) $ tailExprs body

      let ourHeads = case (head headLists) of
            [] -> [head defAssigns]
            headList -> headList
      
      return $ (ourHeads
                ,[]
                ,defAssigns ++ bodyAssigns ++ subNodes
                ,subEdges)
        
    _ -> case (headLists) of
      [] -> return ([], [], subNodes, subEdges) --Means we are a leaf node, no sub-expressions
      _ -> do
        let ourHeads = head headLists
        let ourTails = last tailLists
        return (ourHeads
              , ourTails
               , subNodes
               , subEdges)
        --Other cases don't generate control nodes for one-level analysis
        --For control flow, we just calculate each sub-expression in sequence
        --We connect the end nodes of each sub-expression to the first of the next
   
varAssign :: Pattern -> LabeledExpr -> ControlNode
varAssign pat e = Assign (NormalVar $ getPatternVars pat) e

--type InterNode = ControlNode' (FnLabel Label)

{-
toInterNode :: LabelNode -> InterNode
toInterNode (Call l) = Call $ FnCall l
toInterNode (Return l) = Return $ FnReturn l
toInterNode (ProcEntry l) = ProcEntry $ FnEnter l
toInterNode (ProcExit l) = ProcEntry (FnExit l)
toInterNode (Start l) = Start $ Intra l 
toInterNode (End l) = End $ Intra l
toInterNode GlobalEntry = GlobalEntry
toInterNode GlobalExit = GlobalExit
-}

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

{-
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
-}


oneLevelEdges
  :: Map.Map Var Int
  -> Map.Map Var (ControlNode, ControlNode) --Map of entry and exit nodes
  -> LabeledExpr
  -> Maybe [ControlEdge]
oneLevelEdges = _
    

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

type RDef = (Var, Maybe Label) 

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
{-
--The variables referenced or "killed" in a given expression
expRefs :: LabeledExpr -> [Var]
expRefs =
  foldE
  (extendEnv genericDefVars (\_ -> ()))
  Map.empty
  (\(GenericDef _ exp _) -> [exp])
  (\env (A _ exp) vars -> case exp of
       Var v -> (if (Map.member v env) then [v]  else []) ++ (concat vars)
       _ -> concat vars
       )

refs :: Map.Map Label LabeledExpr -> Label -> [Var]
refs m = expRefs . (m Map.!)
-}

expKills :: LabeledExpr -> [RDef]
expKills =
  foldE
  (extendEnv genericDefVars (\(A (_,l,_ ) _) -> l))
  Map.empty
  (\(GenericDef _ exp _) -> [exp])
  (\env (A _ exp) vars -> case exp of
       Var v ->
         (if (Map.member v env) then [(v, Map.lookup v env)]  else []) ++ (concat vars)
       _ -> concat vars
       )
{-
kills :: Map.Map Label LabeledExpr -> LabelNode -> [RDef]
kills theMap (Start node) = _kills_body
kills theMap (End node) =_kills_body
kills theMap (Call node) =_kills_body
kills theMap (Return node) =_kills_body
kills theMap (ProcEntry node) =_kills_body
kills theMap (ProcExit node) =_kills_body
kills theMap GlobalEntry =_kills_body
kills theMap GlobalExit =_kills_body
-}

--The variables defined, or "generated", by the given expression
expGens :: LabeledExpr -> [Var]
expGens =
  foldE
  (extendEnv genericDefVars (\_ -> ()))
  Map.empty
  (\(GenericDef _ exp _) -> [exp])
  (\env (A _ exp) vars -> case exp of
       Let defs _ -> (concatMap (\(GenericDef pat _ _) -> getPatternVars pat) defs ) ++ (concat vars)
       _ -> concat vars
       )

gens :: Map.Map Label LabeledExpr -> Label -> [Var]
gens m = expGens . (m Map.!)

genericDefVars :: GenericDef a Var -> [Var]
genericDefVars (GenericDef p _ _) = getPatternVars p

--Transfer function for reaching definitions, we find the fixpoint for this
transferFun :: Map.Map Label LabeledExpr -> Label -> ReachingDefs -> ReachingDefs
transferFun labMap label payload = error "TODO transfer fun"
  --payload `latticeJoin` (DirectRelevantVars [])

