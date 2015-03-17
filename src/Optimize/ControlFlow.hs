{-Joseph Eremondi UU# 4229924
  Utrecht University, APA 2015
  Project one: dataflow analysis
 March 17, 2015 -}

{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}
module Optimize.ControlFlow  where

import           AST.Annotation         (Annotated (..))

import           AST.Expression.General
import qualified AST.Module             as Module
import qualified AST.Pattern            as Pattern
import qualified AST.Variable           as Var
import qualified AST.Variable           as Variable
import           Control.Monad
import qualified Data.List              as List
import qualified Data.Map               as Map
import qualified Data.Set               as Set
import           Elm.Compiler.Module
import           Optimize.Environment
import           Optimize.Traversals
import           Optimize.Types

import qualified Data.IntMap            as IntMap
import qualified Elm.Compiler.Module    as PublicModule


import           Data.Char              (isUpper)

import qualified AST.Type               as Type
import           Data.Hashable

-- | Type for variables or some "special cases"
data VarPlus =
  NormalVar Var Label
  | IntermedExpr Label
  | FormalReturn Var
  | ActualParam Label
  | FormalParam Pattern Label
  | Ref Var
  | ExternalParam Int Var
    deriving (Eq, Ord, Show)

-- | Nodes for different types of statements in our control flow graph
-- | We leave the "expression" type generic, for whether we store the expression itself,
-- | Or just its label
data ControlNode' expr =
  Branch (expr)
  | Assign VarPlus (expr)
    --Used for special cases where we assign to internal values, like params or return value
  | AssignParam VarPlus VarPlus (expr)
  | Call  (expr) --list maping Input references to Formal args
  | Return Var [VarPlus] (expr)
  | ProcEntry (expr)
  | ProcExit (expr)
  | ExprEval (expr)
  | ExternalCall Var (expr)
    deriving (Functor, Eq, Ord, Show)

{-|
We use this to make a tree-like structure for monadic code,
which we then integrate into our CFG.
|-}
data TaskStructure =
  Task LabeledExpr
  | TSeq LabeledExpr TaskStructure (Pattern) TaskStructure
  | TBranch LabeledExpr [(LabeledExpr, TaskStructure)]
  | TCase LabeledExpr LabeledExpr [(Pattern, TaskStructure)]
  | TCall LabeledExpr LabeledExpr
  | TLet LabeledExpr [LabelDef] TaskStructure
    deriving (Show)

-- | We use this to store nodes in a HashMap, hopefully
-- | to get some speed increases
instance Hashable ControlNode where
  hashWithSalt _ n = getNodeLabel $ fmap (getLabel) n

-- | We use this to store nodes in a HashMap, hopefully
-- | to get some speed increases
instance Hashable LabelNode where
  hashWithSalt _ = getNodeLabel

-- | Given a node, return the label of the expression represented by that node
-- | or a "special" label if it represents an external function
getNodeLabel :: ControlNode' Label -> Label
getNodeLabel (Branch n) = n
getNodeLabel (ExternalCall _ l) = l
getNodeLabel (Assign _ n2) = n2
getNodeLabel (AssignParam _ _ n2) = n2
getNodeLabel (ExprEval n) = n
getNodeLabel (Call n) = n
getNodeLabel (Return _ _ n2) = n2
getNodeLabel (ProcEntry n) = n
getNodeLabel (ProcExit n) = n
--getNodeLabel _ = Label 0

{-
-- Just Map.!, but printing useful info if the item is not in the map
mapGet :: (Ord k, Show k, Show a) => Map.Map k a -> k -> a
mapGet m k = case Map.lookup k m of
  Nothing -> error $ "Couldn't find key " ++ (show k) ++ " in map " ++ (show $ Map.toList m )
  Just e -> e
-}

labelLook
  :: IntMap.IntMap [ControlNode]
  -> LabeledExpr
  -> Maybe [ControlNode]
labelLook dict expr = IntMap.lookup (getLabel expr) dict

{-|
Information about each function defined in a module.
We need to know this before we construct our control-flow graph.
|-}
data FunctionInfo =
  FunctionInfo
  {
    arity        :: Int,
    formalParams :: [VarPlus],
    entryNode    :: Maybe ControlNode,
    exitNode     :: Maybe ControlNode,
    topFnLabel   :: Maybe Label,
    fnType       :: Maybe Type.CanonicalType
  } -- deriving (Eq, Ord, Show)


type ControlNode = ControlNode' LabeledExpr
type LabelNode = ControlNode' Label

type ControlEdge = (ControlNode, ControlNode)


{-
-- | For a fuction parameter, we treat each tail-position expression in the parameter
-- | As an assignment to the actual value of that parameter
paramNodes :: [LabeledExpr] -> [[ControlNode]]
paramNodes = map (\ arg ->
                         map (\tailExpr ->
                           Assign (ActualParam $ getLabel arg) tailExpr ) $ tailExprs arg)
-}

{-
-- | Get the expressions in "tail" position of an expression
-- | These can be viewed as assignments to the value of the expression
tailExprs :: LabeledExpr -> [LabeledExpr]
tailExprs wholeExp@(A _ e) = tailExprs' e
  where
    tailExprs' (MultiIf guardBodies) = concatMap tailExprs $ map snd guardBodies
    tailExprs' (Case _ cases) = concatMap tailExprs $ map snd cases
    tailExprs' (Let _ body) = tailExprs body
    tailExprs' _ = [wholeExp] --All other cases, the expression itself is the returned value, no control flow


-- | Given a tail position expression, generate the control node
-- | Representing its assigning a value to the expression
tailAssign :: Label ->  LabeledExpr -> ControlNode
tailAssign label tailExpr = Assign (IntermedExpr label) tailExpr
-}


-- | Convert a bin-op to a function call, since the difference is only syntactic
binOpToFn :: LabeledExpr -> LabeledExpr
binOpToFn (A ann (Binop op e1 e2)) =
  let
    opFn = A ann $ Var op
    firstFun = A ann $ App opFn e1
  in A ann $ App firstFun e2

-- | Given two lists of control nodes, add an edge from each node in the first list
-- | to each node on the second list
connectLists :: ([ControlNode], [ControlNode]) -> [ControlEdge]
connectLists (l1, l2) = [(n1, n2) | n1 <- l1, n2 <- l2]



-- | Given an expression, generate the control-flow graph edges from that expression
-- | Without recursing deeper into the expression
-- | We use a dictionary mapping expressions to their "head" and "tail control nodes,
-- | i.e. lists of control nodes that represent entry into evaluating an expression,
-- | and ones that can be the exit-points for evaluating an expression
oneLevelEdges
  :: Map.Map Var FunctionInfo
  -> LabeledExpr
  -> [Maybe (
     IntMap.IntMap [ControlNode]
    ,IntMap.IntMap [ControlNode]--Entry and exit node for sub exps
    --,[ControlNode]
    ,[ControlEdge]) ]
  -> Maybe (
     IntMap.IntMap [ControlNode]

    ,IntMap.IntMap [ControlNode]--Entry and exit node for sub exps
    --,[ControlNode]
    ,[ControlEdge])
oneLevelEdges fnInfo e@(A (_, label, env) expr) maybeSubInfo = do
  (headMaps, tailMaps, {-subNodesL,-} subEdgesL) <- List.unzip3 `fmap` (mapM id maybeSubInfo) --Edges and nodes from our sub-expressions
  --let subNodes = concat subNodesL
  let headMap = IntMap.unions headMaps
  let tailMap = IntMap.unions tailMaps
  let subEdges = concat subEdgesL
  case expr of
    --Function: we have call and return for the call, and evaluating each arg is a mock assignment
    App e1 _ -> do
      fnName <- functionName e1
      argList <- argsGiven e
      let isExternal = case (Var.home fnName) of
            Var.Module _ -> True
            _ -> False
      case (isSpecialFn fnName, isCtor fnName, isExternal) of
        (True, False, _) -> do
          let specialFunResult = specialFnEdges fnInfo (headMap, tailMap) e
          case specialFunResult of
            Just (newHeads, newTails, specialEdges)  ->
              return (newHeads, newTails, subEdges ++ specialEdges)
            Nothing -> return (headMap, tailMap, subEdges)
        (False, True, _) -> case (headMaps) of
          [] -> leafStatement (headMap, tailMap) subEdges e
          _ -> intermedStatement (headMap, tailMap) subEdges e
        (False, False, True) -> do --non-special external call
          let numArgs = length argList
          thisFunInfo <- Map.lookup fnName fnInfo
          let fnArity = arity thisFunInfo
          (ourHead:otherArgHeads) <-
                mapM (labelLook headMap) argList
          argTails <-
                mapM (labelLook tailMap) argList
          --let callNode = Call e
          --let retNode = Return fnName e
          --Generate assignment nodes for the actual parameters to the formals
          let assignFormalNodes =
                map (\(formal, arg) ->
                      Assign formal arg) $ zip (formalParams thisFunInfo) argList
          --Control edges to generate
          let externalCallNode = ExternalCall fnName e
          let calcNextParamEdges =
                concatMap connectLists $ zip (init argTails) otherArgHeads

          let gotoFormalEdges = connectLists (last argTails, [head assignFormalNodes])

          let assignFormalEdges = zip (init assignFormalNodes) (tail assignFormalNodes)
          let callEdges = [(last assignFormalNodes, externalCallNode )]

          --TODO separate labels for call and return?
          let ourTail = AssignParam (IntermedExpr label) (FormalReturn fnName)  e
          let returnEdges = [ (externalCallNode, ourTail)]

          case (fnArity == numArgs) of
                (True) -> return $
                            (IntMap.insert (getLabel e) ourHead headMap,
                             IntMap.insert (getLabel e) [ourTail] tailMap,
                              --[callNode, retNode] ++ (concat argNodes),
                             assignFormalEdges ++ calcNextParamEdges ++ assignFormalEdges ++
                               gotoFormalEdges ++ callEdges ++
                               callEdges ++ returnEdges ++ subEdges  ) --TODO app edges
                --If we haven't applied all the arguments, we just do nothing
                --And hope we'll find the full application further up in the tree
                (False) -> return $ (headMap, tailMap, subEdges)

        _ -> do
          let numArgs = length argList
          let mThisFunInfo = Map.lookup fnName fnInfo
          case (mThisFunInfo) of
            Nothing -> Nothing --Means we found a Native module, so don't optimize
            Just (thisFunInfo) -> do
              let fnArity = arity thisFunInfo
              fnEntryNode <- entryNode thisFunInfo
              fnExitNode <- exitNode thisFunInfo
              let inLocalScope = case (Map.lookup fnName env) of
                    Nothing -> False
                    Just fnLab -> (Just fnLab) == (topFnLabel thisFunInfo)
              (ourHead:otherArgHeads) <-
                    mapM (labelLook headMap) argList
              argTails <-
                    mapM (labelLook tailMap) argList
              let callNode = Call e
              let retNode = case (fnType thisFunInfo) of
                    Nothing -> Return fnName [] e
                    Just ty -> let
                        tyList = functionParamTypes ty
                        refs = [Ref v | (A _ (Var v), argTy) <- zip argList tyList,
                                       isRefTy argTy]
                      in Return fnName refs e
              --Generate assignment nodes for the actual parameters to the formals
              let assignFormalNodes =
                    map (\(formal, arg) ->
                          Assign formal arg) $ zip (formalParams thisFunInfo) argList
              --Control edges to generate

              let calcNextParamEdges =
                    concatMap connectLists $ zip (init argTails) otherArgHeads

              let gotoFormalEdges = connectLists (last argTails, [head assignFormalNodes])

              let assignFormalEdges = zip (init assignFormalNodes) (tail assignFormalNodes)
              let callEdges = [(last assignFormalNodes, callNode ),
                              (callNode, fnEntryNode)]

              --TODO separate labels for call and return?
              let ourTail = AssignParam (IntermedExpr label) (FormalReturn fnName)  e
              let returnEdges = [ (fnExitNode, retNode)
                    ,(retNode, ourTail)
                    ]
                --TODO add edges to function entry, assigning formals
          --TODO check for shadowing?
              case (fnArity == numArgs, inLocalScope) of
                (True, False) -> return $
                            (IntMap.insert (getLabel e) ourHead headMap,
                             IntMap.insert (getLabel e) [ourTail] tailMap,
                              --[callNode, retNode] ++ (concat argNodes),
                             assignFormalEdges ++ calcNextParamEdges ++ assignFormalEdges ++
                               gotoFormalEdges ++ callEdges ++
                               callEdges ++ returnEdges ++ subEdges  ) --TODO app edges
                --If we haven't applied all the arguments, we just do nothing
                --And hope we'll find the full application further up in the tree
                (False, False) -> return (headMap, tailMap, subEdges)

                _ ->  Nothing
            --If function is locally defined, or not fully instantiated, we fail
    Lambda _ _ ->  Nothing
    Binop op e1 e2 -> case (isArith op) of
      True -> case (headMaps) of
        [] -> leafStatement (headMap, tailMap) subEdges e
        _ -> intermedStatement (headMap, tailMap) subEdges e  --Arithmetic doesn't need its own statements, since we can do inline
      False -> oneLevelEdges fnInfo (binOpToFn e) maybeSubInfo
    --Data _ args -> paramNodes args --Ctor is a constant, so just evaluate the arguments
    MultiIf condCasePairs -> do
      --We treat each case of the if expression as an assignment to the final value
      --of the if expression
      let guards = (map fst condCasePairs)
      let bodies = map snd condCasePairs
      --let bodyTails = concatMap tailExprs bodies
      --let guardNodes = map Branch guards
      bodyHeads <- mapM (labelLook headMap) bodies
      bodyTails <- mapM (labelLook tailMap) bodies
      --Each guard is connected to the next guard, and the "head" control node of its body
      (ourHead:otherGuardHeads) <- mapM (labelLook headMap ) guards
      guardTails <- mapM (labelLook tailMap ) guards
      --let notLastGuardEnds = init guardEnds


      let guardFallthroughEdges = concatMap connectLists $ zip (init guardTails) otherGuardHeads
      let guardBodyEdges = concatMap connectLists $ zip guardTails bodyHeads

      let bodyAssigns = map (\bod ->[(Assign (IntermedExpr (getLabel e)) bod) ]) bodies

      let endEdges = concatMap connectLists $ zip bodyTails bodyAssigns
      let ourTail = concat bodyAssigns
      return (
        IntMap.insert (getLabel e) ourHead headMap --First statement is eval first guard
         ,IntMap.insert (getLabel e) ourTail tailMap --Last statements are any tail exps of bodies
        --,guardNodes ++ bodyNodes ++ subNodes
         ,subEdges ++ guardBodyEdges ++ guardFallthroughEdges  ++ endEdges)
    Case caseExpr patCasePairs -> do
      --We treat each case of the case expression as an assignment to the final value
      --of the case expression
      --Those assignments correspond to the expressions in tail-position of the case
      let cases = map snd patCasePairs

      let assignCaseValueNodes =  map (\caseBody -> [Assign (IntermedExpr $ getLabel e) caseBody] ) cases

      let branchNode = Branch e
      --let ourHead = case (headMap `mapGet` (getLabel caseExpr)) of
      --      [] -> [Assign (IntermedExpr $ getLabel caseExpr) caseExpr]
      --      headList -> headList
      ourHead <- labelLook headMap caseExpr

      caseHeadNodes <- concat `fmap` mapM (labelLook tailMap ) cases
      caseTailNodes <- mapM (labelLook  tailMap) cases
      caseTails <- labelLook tailMap caseExpr
      let exprToBranchEdges =
            connectLists (caseTails, [branchNode])
      let branchToCaseEdges =  connectLists ([branchNode], caseHeadNodes)

      let toAssignEdges = concatMap connectLists $ zip caseTailNodes assignCaseValueNodes


      return $ (IntMap.insert (getLabel e) ourHead headMap
         --Last thing is assignment for whichever case we took
                ,IntMap.insert (getLabel e) (concat assignCaseValueNodes) tailMap
        --,[Assign (IntermedExpr $ getLabel caseExpr) caseExpr] ++ caseNodes ++ subNodes
         ,subEdges ++ exprToBranchEdges ++ branchToCaseEdges ++ toAssignEdges)
    Let defs body -> do
      --We treat the body of a let statement as an assignment to the final value of
      --the let statement
      --Those assignments correspond to the expressions in tail-position of the body
      let orderedDefs = defs --TODO sort these
      --For each def, we make an assignment giving the body's value to each variable
      let getDefAssigns (GenericDef pat b _) =
             (varAssign  pat) $ b
      let defAssigns = map getDefAssigns orderedDefs
      --let bodyAssigns = map (tailAssign $ getLabel e) $ tailExprs body

      (ourHead:otherHeads) <-
            mapM (\(GenericDef _ b _) -> labelLook headMap b) orderedDefs
      rhsDefTails <-
            mapM (\(GenericDef _ b _) -> labelLook tailMap b) orderedDefs

      let lastAssignInDefs = map  (\defList->[last defList] ) defAssigns
      let firstAssignInDefs = map (\defList->[head defList] ) defAssigns

      bodyHead <- labelLook headMap body

      bodyTail <- labelLook tailMap body
      let ourTail = [Assign (IntermedExpr (getLabel e)) body]

      let defTailToFirstAssignEdges =
            concatMap connectLists $ zip rhsDefTails firstAssignInDefs
      let assignWithinDefEdges =
            concatMap (\assigns -> zip (tail assigns) (init assigns)) defAssigns

      let betweenDefEdges =
            concatMap connectLists $ zip lastAssignInDefs (otherHeads ++ [bodyHead])
      let assignExprEdges = connectLists (bodyTail, ourTail)

      --TODO need intermediate?

      return $ (IntMap.insert (getLabel e) ourHead headMap
                ,IntMap.insert (getLabel e) ourTail tailMap
                --,defAssigns ++ bodyAssigns ++ subNodes
                ,subEdges ++ betweenDefEdges
                 ++ defTailToFirstAssignEdges ++ assignWithinDefEdges ++ assignExprEdges)

    _ -> case (headMaps) of
      [] -> leafStatement (headMap, tailMap) subEdges e
      _ -> intermedStatement (headMap, tailMap) subEdges e

--TODO doc each case

leafStatement
    :: (IntMap.IntMap [ControlNode], IntMap.IntMap [ControlNode])
                       -> [ControlEdge]
                       -> LabeledExpr
                       -> Maybe (IntMap.IntMap [ControlNode],
                             IntMap.IntMap [ControlNode],
                             [ControlEdge])
leafStatement (headMap, tailMap) subEdges e = do
        let ourHead = [ExprEval e]
        let ourTail = ourHead
        return (IntMap.insert (getLabel e) ourHead headMap,
                IntMap.insert (getLabel e) ourTail tailMap,
                subEdges) --Means we are a leaf node, no sub-expressions

intermedStatement
  :: (IntMap.IntMap [ControlNode], IntMap.IntMap [ControlNode])
                       -> [ControlEdge]
                       -> LabeledExpr
                       -> Maybe (IntMap.IntMap [ControlNode],
                             IntMap.IntMap [ControlNode],
                             [ControlEdge])
intermedStatement (headMap, tailMap) subEdges e =
  do
        --TODO need each sub-exp?
        let subExprs = (directSubExprs e) :: [LabeledExpr]
        subHeads <-  mapM (labelLook headMap) subExprs
        subTails <- mapM (labelLook tailMap) subExprs
        let ourHead = head subHeads
        let ourTail = last subTails
        let subExpEdges = concatMap connectLists $ zip (init subTails) (tail subHeads)
        return
          (IntMap.insert (getLabel e) ourHead headMap
              , IntMap.insert (getLabel e) ourTail tailMap
               --, subNodes
               , subEdges ++ subExpEdges)


{-|
Given a top-level definition, traverse the expression for that definition
and return all control-flow edges defined by it.
|-}
allDefEdges
  :: Map.Map Var FunctionInfo
  -> LabelDef
  -> Maybe (
    IntMap.IntMap [ControlNode],
    IntMap.IntMap [ControlNode],
    [(ControlNode, ControlNode)] )
allDefEdges fnInfo d@(GenericDef pat body ty) =
  if (isStateMonadFn ty)
  then monadicDefEdges fnInfo d
  else allExprEdges fnInfo $ functionBody body

{-|
Given an expression, traverse it
and return all control-flow edges defined by it.
|-}
allExprEdges
  :: Map.Map Var FunctionInfo
  -> LabeledExpr
  -> Maybe (
    IntMap.IntMap [ControlNode],
    IntMap.IntMap [ControlNode],
    [(ControlNode, ControlNode)] )
allExprEdges fnInfo e =
  foldE
           (\ _ () -> repeat ())
           ()
           (\(GenericDef _ e v) -> [e])
           (\ _ e subs-> oneLevelEdges fnInfo e subs)
           e

-- | Convert a string to a canonical local variable
nameToCanonVar :: String -> Var
nameToCanonVar name = Variable.Canonical  Variable.Local name

{-|
Given a function definition, generate the special control flow
edges representing proc entry and exit, as well as assigning parameters
and return values.
We need the map of head and tail nodes so that we can connect our special edges
to the function body.
|-}
functionDefEdges
  :: ( IntMap.IntMap [ControlNode]
    , IntMap.IntMap [ControlNode])
  -> LabelDef
  -> Maybe [ControlEdge]
functionDefEdges
  (headMap, tailMap)
  (GenericDef (Pattern.Var name)
  e@(A (_,label,_) _) _ty ) =  do
      let body = functionBody e
      let argPats = (functionArgPats e)
      let argLabels = (functionArgLabels e)
      let argPatLabels = zip argPats argLabels
      --let argVars = concatMap getPatternVars argPats
      let ourHead = ProcEntry e
      let ourTail = [ProcExit e]
      bodyHead <- labelLook headMap body
      --let bodyTails = tailExprs body
      tailNodes <-  labelLook tailMap body
      let assignReturns = [AssignParam
                            (FormalReturn (nameToCanonVar name) )
                            (IntermedExpr $ getLabel body) body]
      let assignParams =
            [(AssignParam (FormalParam pat label) (NormalVar v argLab) body) |
               (pat,argLab) <- argPatLabels, v <- getPatternVars pat]
      let (startEdges, assignFormalEdges, gotoBodyEdges) =
            case argPats of
              [] -> (connectLists([ourHead], bodyHead),
                    [], [])
              _ -> ([(ourHead, head assignParams )],
                  zip (init assignParams) (tail assignParams),
                  connectLists ([last assignParams], bodyHead))
      let assignReturnEdges = connectLists (tailNodes, assignReturns)
      let fnExitEdges = connectLists (assignReturns, ourTail)

      return $ startEdges ++ assignFormalEdges ++
        assignReturnEdges ++ fnExitEdges ++ gotoBodyEdges

{-|
--Given a monadic structure, create control-flow edges for each statement
|-}
monadStructureEdges fnInfo taskStruct =
  case taskStruct of
    Task s -> do
      (headMap, tailMap, subEdges) <- allExprEdges fnInfo s
      ourHead <- labelLook headMap s
      ourTail <- labelLook tailMap s
      return (ourHead,
              ourTail,
              IntMap.insert (getLabel s) ourHead headMap,
              IntMap.insert (getLabel s) ourTail tailMap,
              subEdges)
    TSeq ourExpr s1 (pat) s2 ->  do
      let ourLabel = getLabel ourExpr
      (ourHead, innerTail, hm1, tm1, edges1) <- monadStructureEdges fnInfo s1
      (innerHead, ourTail, hm2, tm2, edges2) <- monadStructureEdges fnInfo s2
      let assignNodes =
            [Assign (NormalVar var (getLabel ourExpr)) ourExpr
             | var <- getPatternVars pat]
      let (gotoAssignEdges, insideAssignEdges, gotoNextEdges) = case assignNodes of
            [] -> (connectLists (innerTail, innerHead), [], [])
            _ -> (connectLists (innerTail, [head assignNodes]),
                 zip (init assignNodes) (tail assignNodes),
                 connectLists ([last assignNodes], innerHead))
      return (ourHead,
              ourTail,
              IntMap.insert ourLabel ourHead $ IntMap.union hm1 hm2,
              IntMap.insert ourLabel ourTail $ IntMap.union tm1 tm2,
              edges1 ++ edges2 ++ gotoAssignEdges ++ insideAssignEdges ++ gotoNextEdges)
    TBranch ourExpr guardStatementPairs -> do
      let ourLabel = getLabel ourExpr
      infoList <- mapM
        (\(g, s) -> do
            gInfo <- allExprEdges fnInfo g
            sInfo <- monadStructureEdges fnInfo s
            return (gInfo, sInfo)) guardStatementPairs
      let branchNodes = map (\g -> [Branch g]) $ map fst guardStatementPairs
      let (headMap, tailMap, nonMonadEdges) =
            List.foldl' (\ (headSoFar, tailSoFar, edgesSoFar) (h1,t1,e1) ->
                     (IntMap.union headSoFar h1,
                     IntMap.union tailSoFar t1,
                     edgesSoFar ++ e1)) (IntMap.empty, IntMap.empty, [] ) $ map fst infoList
      guardHeads <- mapM (labelLook headMap) $ map fst guardStatementPairs
      guardTails <- mapM (labelLook tailMap) $ map fst guardStatementPairs
      let bodyHeads = map (\(h,_,_,_,_) -> h) $ map snd infoList
      let bodyTails = map (\(_,t,_,_,_) -> t) $ map snd infoList
      let subEdges = nonMonadEdges ++ ( concatMap (\(_,_,_,_,e) -> e) $ map snd infoList)
      let ourHead = head guardHeads
      let guardToBranchEdges = concatMap connectLists $ zip guardTails branchNodes
      let branchToBodyEdges = concatMap connectLists $ zip branchNodes bodyHeads
      --List should never be empty
      let interGuardEdges = concatMap connectLists $ zip (init branchNodes) (tail guardHeads)
      let ourTails = concat bodyTails
      let (mHeadMaps, mTailMaps) = unzip $ map (\(_,_,h,t,_) -> (h,t)) $ map snd infoList
      let newHeadMap = IntMap.union headMap $ IntMap.unions mHeadMaps
      let newTailMap = IntMap.union tailMap $ IntMap.unions mTailMaps

      return (ourHead,
              ourTails,
              IntMap.insert ourLabel ourHead newHeadMap,
              IntMap.insert ourLabel ourTails newTailMap,
              subEdges ++ guardToBranchEdges ++ interGuardEdges ++ branchToBodyEdges)

    TCase ourExpr caseExp patStmtPairs -> do
      let ourLabel = getLabel ourExpr
      (headMap, tailMap, nonMonadicEdges) <- allExprEdges fnInfo caseExp
      ourHead <- labelLook headMap caseExp
      bodyTails <- labelLook tailMap caseExp
      infoList <- mapM (monadStructureEdges fnInfo) $ map snd patStmtPairs
      let branchNode = [Branch ourExpr]
      let subEdges = nonMonadicEdges ++ (concatMap (\(_,_,_,_,e) -> e) infoList )
      let gotoBranchEdges = connectLists (bodyTails, branchNode)
      let gotoArmEdges = concatMap (\(h,_,_,_,_) -> connectLists (branchNode, h)) infoList
      let ourTails = concatMap (\(_,t,_,_,_) -> t) infoList
      let (mHeadMaps, mTailMaps) = unzip $ map (\(_,_,h,t,_) -> (h,t)) infoList
      let newHeadMap = IntMap.union headMap $ IntMap.unions mHeadMaps
      let newTailMap = IntMap.union tailMap $ IntMap.unions mTailMaps

      return (ourHead,
              ourTails,
              IntMap.insert ourLabel ourHead newHeadMap,
              IntMap.insert ourLabel ourTails newTailMap,
              subEdges ++ gotoArmEdges ++ gotoBranchEdges)
    --TODO get rid of call?
    TCall ourExpr app -> do
      let ourLabel = getLabel ourExpr
      (headMap, tailMap, subEdges) <- allExprEdges fnInfo app
      ourHead <- labelLook headMap app
      ourTail <- labelLook tailMap app
      return (ourHead
              , ourTail
              , IntMap.insert ourLabel ourHead headMap
              , IntMap.insert ourLabel ourTail tailMap
              , subEdges)
    TLet ourExp defs bodyStmt -> do
      let getDefAssigns (GenericDef pat b _) =
             (varAssign  pat) $ b
      let defAssigns = map getDefAssigns defs
      --let bodyAssigns = map (tailAssign $ getLabel e) $ tailExprs body
      let rhses = map (\(GenericDef _ b _) -> b) defs
      nonMonadicInfo <- mapM (allExprEdges fnInfo) rhses
      let (headMap, tailMap, nonMonadEdges) =
            List.foldl' (\ (headSoFar, tailSoFar, edgesSoFar) (h1,t1,e1) ->
                     (IntMap.union headSoFar h1,
                     IntMap.union tailSoFar t1,
                     edgesSoFar ++ e1)) (IntMap.empty, IntMap.empty, [] ) $ nonMonadicInfo


      (ourHead:otherHeads) <-
            mapM (\(GenericDef _ b _) -> labelLook headMap b) defs
      rhsDefTails <-
            mapM (\(GenericDef _ b _) -> labelLook tailMap b) defs

      let lastAssignInDefs = map  (\defList->[last defList] ) defAssigns
      let firstAssignInDefs = map (\defList->[head defList] ) defAssigns

      (bodyHead, bodyTail, subHeads, subTails, monEdges) <-
        monadStructureEdges fnInfo bodyStmt

      --let ourTail = [Assign (IntermedExpr (getLabel e)) body]

      let defTailToFirstAssignEdges =
            concatMap connectLists $ zip rhsDefTails firstAssignInDefs
      let assignWithinDefEdges =
            concatMap (\assigns -> zip (tail assigns) (init assigns)) defAssigns

      let betweenDefEdges =
            concatMap connectLists $ zip lastAssignInDefs (otherHeads ++ [bodyHead])
      return $ (ourHead,
                bodyTail,
                IntMap.insert (getLabel ourExp) ourHead $ IntMap.union headMap subHeads,
                IntMap.insert (getLabel ourExp) bodyTail $ IntMap.union tailMap subTails,
                nonMonadEdges ++ monEdges ++ defTailToFirstAssignEdges
                  ++ assignWithinDefEdges ++ betweenDefEdges

        )



{-|
--Given a monadic expression, break it up into statements
--And calculate the edges between those statements in our CFG
--TODO self recursion?
--TODO nested state monads?
|-}
monadicDefEdges
  :: Map.Map Var FunctionInfo
  -> LabelDef
  -> Maybe (
    IntMap.IntMap [ControlNode],
    IntMap.IntMap [ControlNode],
    [(ControlNode, ControlNode)] )
monadicDefEdges fnInfo (GenericDef (Pattern.Var fnName) e _) =  do
  let body = functionBody e
  let taskStruct = sequenceMonadic body
  (_,_,headMap, tailMap, subEdges) <-
    monadStructureEdges fnInfo taskStruct
  return (headMap, tailMap, subEdges)

-- | Given the pattern of a definition's LHS
-- | and the expression on the RHS,
-- | generate the control nodes assigning to all variables defined
-- | in the definition
varAssign :: Pattern -> LabeledExpr -> [ControlNode]
varAssign  pat e = [Assign (NormalVar pvar (getLabel e)  ) e |
                   pvar <- getPatternVars pat]

-- | Given an expression representing a function application, return the expression
-- | Representing the function to be called, if it can be resolved to a specific name
functionName :: LabeledExpr -> Maybe Var
functionName (A _ e) = case e of
  Var v -> Just v
  (App f _ ) -> functionName f
  _ ->  Nothing

-- | Given a function definition, return the expression for the body of that function.
-- | We deal with multi-parameter functions by recursing into expresions until we find
-- | a body that isn't a Lambda
functionBody :: LabeledExpr -> LabeledExpr
functionBody (A _ (Lambda _ e)) = functionBody e
functionBody e = e

-- | Given a function definition, return the label of the body of that function
functionLabel (GenericDef _ body _) = case functionBody body of
  (A (_, label, _) _) -> label

-- | Given a function definition, return all patterns corresponding to
-- | arguments of that function
functionArgPats :: LabeledExpr -> [Pattern]
functionArgPats (A _ (Lambda pat e)) = [pat] ++ (functionArgPats e)
functionArgPats _ = []

-- | Given a function definition, return the labels of each lambda expresssion
-- | defining a single argument
functionArgLabels :: LabeledExpr -> [Label]
functionArgLabels (A (_,l,_) (Lambda pat e)) = [l] ++ (functionArgLabels e)
functionArgLabels _ = []

functionArgsAndAnn :: LabeledExpr -> [(Pattern, (Region, Label, Env Label))]
functionArgsAndAnn (A ann (Lambda pat e)) = [(pat, ann)] ++ (functionArgsAndAnn e)
functionArgsAndAnn _ = []

functionParamTypes :: Type.CanonicalType -> [Type.CanonicalType]
functionParamTypes (Type.Lambda arg ret) = [arg] ++ functionParamTypes ret
functionParamTypes _ = []

-- | Get the "final" return type of a function type
-- | i.e. what's returned if it is fully applied
functionFinalReturnType :: Type.CanonicalType -> Type.CanonicalType
functionFinalReturnType t@(Type.Lambda _ ret) = functionFinalReturnType ret
functionFinalReturnType t = t

-- | Our special State monad for imperative code
stateMonadTycon = Type.Type $ Var.Canonical {Var.home = Var.Module ["State","Escapable"], Var.name = "EState"}

-- | Check if a function type is "monadic" for our state monad
-- | We take maybe as an argument so that we can pass the type stored in a defintion
isStateMonadFn :: Maybe Type.CanonicalType -> Bool
isStateMonadFn (Just ty) = case (functionFinalReturnType ty) of
  (Type.App tyCon _) -> tyCon == stateMonadTycon
  _ -> False
isStateMonadFn _ =  False

-- | Given a monadic function, sequence it into a series of "statements"
-- | Based on the `andThen` bind operator, used in infix position
-- | We return a list of expressions representing statement, paired
-- | with the pattern and expression that the result of that statement is stored in
-- | using a monadic bind.
-- | We also return the last statement, whose value is the result of the monadic computation.
sequenceMonadic :: LabeledExpr
                -> TaskStructure
sequenceMonadic e@(A _ (Binop op e1 (A _ (Lambda pat body)) )) =
  case (Var.name op) of
    "andThen" -> let
        bodySeq = sequenceMonadic body
        headSeq = sequenceMonadic e1
      in TSeq e headSeq pat bodySeq
    _ -> Task e
--sequenceMonadic e@(A _ (App _ _)) = TCall e e
sequenceMonadic e@(A _ (MultiIf guardCasePairs)) =
  TBranch e $ map (\(g, body) -> (g, (sequenceMonadic body))) guardCasePairs
sequenceMonadic e@(A _ (Let defs body)) =
  TLet e defs $ sequenceMonadic body
sequenceMonadic e@(A _ (Case caseExp patCasePairs)) =
  TCase e caseExp $ map (\(pat, arm) -> (pat, sequenceMonadic arm)) patCasePairs
sequenceMonadic e = Task e

-- | Return the number of arguments a function takes by counting its lambdas
getArity :: LabeledExpr -> Int
getArity (A _ (Lambda _ e)) = 1 + (getArity e)
getArity e = 0

-- | Return the number of arguments a function type takes by counting its arrows
tyArity :: Type.CanonicalType -> Int
tyArity (Type.Lambda _ e) = 1 + (tyArity e)
tyArity _ = 0

-- | Given a call expression, determine how many arguments we've supplied to it
argsGiven :: LabeledExpr -> Maybe [LabeledExpr]
argsGiven (A _ e) = case e of
  Var v -> Just []
  (App f e ) -> (++[e]) `fmap` argsGiven f
  _ ->  Nothing

--TODO qualify?
-- | Names of special monadic functions whose actions correspond to special control nodes
-- | For example, writeRef corresponds to an assignment
specialFnNames = Set.fromList [
  Variable.Canonical (Variable.Module ["State", "Escapable"]) "newRef"
  , Variable.Canonical (Variable.Module ["State", "Escapable"]) "deRef"
  , Variable.Canonical (Variable.Module ["State", "Escapable"]) "writeRef"
  ]

--TODO add module?
-- | Determine if a function is one of our special monadic names
isSpecialFn :: Var -> Bool
isSpecialFn v =  Set.member v specialFnNames

-- | Generate the control flow edges with a call to a special monadic function
specialFnEdges
  :: Map.Map Var FunctionInfo
  -> (IntMap.IntMap [ControlNode], IntMap.IntMap [ControlNode])
  -> LabeledExpr
  -> Maybe (IntMap.IntMap [ControlNode], IntMap.IntMap [ControlNode], [ControlEdge])
specialFnEdges fnInfo (headMap, tailMap) e@(A _ expr) = do
  fnName <- functionName e
  argList <- argsGiven e
  (firstHead: otherArgHeads) <- mapM (labelLook headMap) argList
  argTails <- mapM (labelLook tailMap)  argList
  --let argNodes = paramNodes argList
  --let assignParamEdges = concatMap connectLists $ zip tailLists argNodes
  let calcNextParamEdges = concatMap connectLists $ zip (init argTails) otherArgHeads
  ourTail <- case (Var.name fnName) of
    --We pass on our monadic value by writing to the "value" of the statement
    "newRef" -> return $
      [AssignParam
       (IntermedExpr $ getLabel e)
       (IntermedExpr (getLabel $ head argList))
       e]
    "deRef" -> case argList of
        [(A _ (Var ref))] -> return $ [AssignParam (IntermedExpr $ getLabel e) (Ref ref) e]
        _ ->  Nothing
    "writeRef" -> case argList of
        [(A _ (Var ref)), otherArg] -> return $ [Assign (Ref ref) e]
        _ -> Nothing
    _ -> Nothing
  --TODO connect our tail to the params tail
  let goToTailEdges = connectLists (last argTails, ourTail)
  return (IntMap.insert (getLabel e) firstHead headMap,
          IntMap.insert (getLabel e) ourTail tailMap,
          calcNextParamEdges ++ goToTailEdges) --TODO need assign param?

-- | Given an operator, return whether it is arithmetic, or if it needs to be
-- | treated as a function call
isArith :: Var -> Bool
isArith = (`elem` arithVars )

isRefTy :: Type.CanonicalType -> Bool
isRefTy (Type.App (Type.Var n) _) =
  n ==  "StateRef"
isRefTy _ = False

-- | The list of binary operators with arithmetic values, who we can treat as instructions
-- | and not as function calls
arithVars = [
  Variable.Canonical (Variable.Module ["Basics"]) "+"
  ,Variable.Canonical (Variable.Module ["Basics"]) "-"
  ,Variable.Canonical (Variable.Module ["Basics"]) "*"
  ,Variable.Canonical (Variable.Module ["Basics"]) "/"
  ,Variable.Canonical (Variable.Module ["Basics"]) "&&"
  ,Variable.Canonical (Variable.Module ["Basics"]) "||"
  ,Variable.Canonical (Variable.Module ["Basics"]) "^"
  ,Variable.Canonical (Variable.Module ["Basics"]) "//"
  ,Variable.Canonical (Variable.Module ["Basics"]) "rem"
  ,Variable.Canonical (Variable.Module ["Basics"]) "%"
  ,Variable.Canonical (Variable.Module ["Basics"]) "<"
  ,Variable.Canonical (Variable.Module ["Basics"]) ">"
  ,Variable.Canonical (Variable.Module ["Basics"]) "<="
  ,Variable.Canonical (Variable.Module ["Basics"]) ">="
  ,Variable.Canonical (Variable.Module ["Basics"]) "=="
  ,Variable.Canonical (Variable.Module ["Basics"]) "/="
            ]

makeCtorType :: String -> [String] -> String -> [Type.CanonicalType] -> Type.CanonicalType
makeCtorType typeName typeVars ctorName ctorArgs =
  foldr addArg endType ctorArgs
    where
      addArg arg tySoFar = Type.Lambda arg tySoFar
      canonVars = map (\s -> Type.Var $ s) typeVars
      endType = Type.App (Type.Type $ nameToCanonVar typeName) canonVars

{-|
Given the interfaces for modules which have ben imported, whose code we don't have
access to, look at the definitions and construct the function information
for all external functions.
|-}
interfaceFnInfo :: Map.Map Name PublicModule.Interface -> Map.Map Var FunctionInfo
interfaceFnInfo interfaces = let
    nameIfaces = Map.toList interfaces
    nameSets = [(extModName, fnName, iface) | (extModName, iface) <- nameIfaces,
                                     (Var.Value fnName) <- Module.iExports iface]

  in Map.fromList $ map
     (\(extModName, fnName, iface)  -> let
                       fnTy = (Module.iTypes iface) Map.! fnName
                       fnArity = tyArity fnTy
                       (Name modStrings) = extModName
                       varName = Var.Canonical (Var.Module modStrings) fnName
                       fParams = map (\n -> ExternalParam n varName) [1 .. fnArity]
                     in (varName, FunctionInfo {
                       arity = fnArity,
                       formalParams = fParams, -- [VarPlus],
                       entryNode = Nothing, -- :: ControlNode,
                       exitNode = Nothing, -- :: ControlNode,
                       topFnLabel = Nothing,
                       fnType = Map.lookup fnName (Module.iTypes iface)})) nameSets

-- |If a function name starts with a capital letter, it's a constructor
-- | So we don't do anything control flowy, we just package the values
isCtor :: Var -> Bool
isCtor v = isUpper (head $ Var.name v)
