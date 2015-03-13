{-# LANGUAGE DeriveFunctor #-}
module Optimize.ControlFlow  where

import           AST.Annotation             (Annotated (..))
import qualified AST.Expression.Canonical   as Canon
import           AST.Expression.General
import qualified AST.Module                 as Module
import qualified AST.Pattern                as Pattern
import           AST.Variable               (Home (..), home)
import qualified AST.Variable               as Var
import           Control.Monad
import qualified Data.List                  as List
import qualified Data.Map                   as Map hiding ((!))
import qualified Data.Set                   as Set
import           Elm.Compiler.Module
import           Optimize.Traversals

import qualified AST.Variable               as Variable

import           Optimize.Environment
import           Optimize.MonotoneFramework
import           Optimize.Types

import qualified Elm.Compiler.Module        as PublicModule



import qualified AST.Type                   as Type

import           Debug.Trace                (trace)
--trace _ x = x

--Type for variables or some "special cases"
data VarPlus =
  NormalVar Var Label
  | IntermedExpr Label
  | FormalReturn Var
  | ActualParam Label
  | FormalParam Pattern Label
  | Ref Var
  | ExternalParam Int Var
    deriving (Eq, Ord, Show)
--TODO how to make sure all our IntermedExprs are there?

--Our different types of control nodes
data ControlNode' expr =
  Branch (expr)
  | Assign VarPlus (expr)
  | AssignParam VarPlus VarPlus (expr)
  | Call (expr)
  | Return Var (expr) --TODO assign to what?
  | ProcEntry (expr)
  | ProcExit (expr)
  | ExprEval (expr)
  | ExternalCall Var [VarPlus]
  | ExternalStateCall Var [VarPlus]
  -- | GlobalEntry --Always the first node
  -- | GlobalExit --Always the last node
    deriving (Functor, Eq, Ord, Show)




getNodeLabel :: ControlNode' Label -> Label
getNodeLabel (Branch n) = n
getNodeLabel (ExternalCall _ _) = Label 0 --TODO better default?
getNodeLabel (ExternalStateCall _ _) = Label 0 --TODO better default?
getNodeLabel (Assign _ n2) = n2
getNodeLabel (AssignParam _ _ n2) = n2
getNodeLabel (ExprEval n) = n
getNodeLabel (Call n) = n
getNodeLabel (Return _ n2) = n2
getNodeLabel (ProcEntry n) = n
getNodeLabel (ProcExit n) = n
--getNodeLabel _ = Label 0


mapGet :: (Ord k, Show k, Show a) => Map.Map k a -> k -> a
mapGet m k = case Map.lookup k m of
  Nothing -> error $ "Couldn't find key " ++ (show k) ++ " in map " ++ (show $ Map.toList m )
  Just e -> e

data FunctionInfo =
  FunctionInfo
  {
    arity        :: Int,
    formalParams :: [VarPlus],
    entryNode    :: ControlNode,
    exitNode     :: ControlNode,
    topFnLabel   :: Maybe Label
  } -- deriving (Eq, Ord, Show)


type ControlNode = ControlNode' LabeledExpr
type LabelNode = ControlNode' Label

type ControlEdge = (ControlNode, ControlNode)



--getLabel :: LabeledExpr -> Label
--getLabel (A (_,l,_) _) = l


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
oneLevelEdges fnInfo e@(A (_, label, env) expr) maybeSubInfo = trace "One Level Defs\n" $ do
  (headMaps, tailMaps, {-subNodesL,-} subEdgesL) <- List.unzip3 `fmap` (mapM id maybeSubInfo) --Edges and nodes from our sub-expressions
  --let subNodes = concat subNodesL
  let headMap = Map.unions headMaps
  let tailMap = Map.unions tailMaps
  let subEdges = concat subEdgesL
  case expr of
    --Function: we have call and return for the call, and evaluating each arg is a mock assignment
    App e1 _ -> trace "App case" $ do
      fnName <- functionName e1
      argList <- argsGiven e
      case (isSpecialFn fnName) of
        True -> do
          (newHeads, newTails, specialEdges) <- specialFnEdges fnInfo (headMap, tailMap) e
          return (newHeads, newTails, subEdges ++ specialEdges)
        False -> do
          let numArgs = length argList
          let mThisFunInfo = Map.lookup fnName fnInfo
          case (mThisFunInfo) of
            Nothing -> Nothing --Means we found a Native module, so don't optimize
            Just (thisFunInfo) -> do
              let fnArity = arity thisFunInfo
              let inLocalScope = case (Map.lookup fnName env) of
                    Nothing -> False
                    Just fnLab -> (Just fnLab) == (topFnLabel thisFunInfo)
              let argNodes = paramNodes argList
              let callNode = Call e
              let retNode = Return fnName e
              --Generate assignment nodes for the actual parameters to the formals
              let assignFormalNodes =
                    map (\(formal, arg) -> Assign formal arg) $ zip (formalParams thisFunInfo) argList
              --Control edges to generate
              let firstHead = (headMap `mapGet` (getLabel $ head argList))
              let otherHeads = map (\arg -> headMap `mapGet` (getLabel $ arg) ) $ tail argList
              let tailLists = map (\arg -> tailMap `mapGet` (getLabel $ arg) )  argList
              let (assignParamEdges, calcNextParamEdges, gotoFormalEdges) =
                    case argList of
                      [] -> error "Fn Call with no argument"
                      _ -> (concatMap connectLists $ zip tailLists argNodes,
                           concatMap connectLists $ zip (init argNodes) otherHeads,
                           connectLists ((last argNodes), [head assignFormalNodes]))

              let assignFormalEdges = zip (init assignFormalNodes) (tail assignFormalNodes)
              let callEdges = [(last assignFormalNodes, callNode ),
                              (callNode, entryNode thisFunInfo)]

              --TODO separate labels for call and return?
              let ourTail = AssignParam (IntermedExpr label) (FormalReturn fnName)  e
              let returnEdges =
                    [ (exitNode thisFunInfo, retNode)
                    ,(retNode, ourTail)
                    ]
                --TODO add edges to function entry, assigning formals
          --TODO check for shadowing?
              case (fnArity == numArgs, inLocalScope) of
                (True, False) -> return $
                            (Map.insert (getLabel e) firstHead headMap,
                             Map.insert (getLabel e) [ourTail] tailMap,
                              --[callNode, retNode] ++ (concat argNodes),
                             assignParamEdges ++ calcNextParamEdges ++ assignFormalEdges ++
                               gotoFormalEdges ++ callEdges ++
                               callEdges ++ returnEdges ++ subEdges  ) --TODO app edges
                --If we haven't applied all the arguments, we just do nothing
                --And hope we'll find the full application further up in the tree
                (False, False) -> return $ (headMap, tailMap, subEdges)

                _ -> Nothing
            --If function is locally defined, or not fully instantiated, we fail
    Lambda _ _ -> trace "!!!Lambda def" $  Nothing
    Binop op e1 e2 -> case (isArith op) of
      True -> case (headMaps) of --If arithmetic, treat like a normal expression, doesn't change control flow
         [] -> (trace "Leaf case" ) $ do
        
           let ourHead = [ExprEval e]
           let ourTail = ourHead
           return (Map.insert (getLabel e) ourHead headMap,
                   Map.insert (getLabel e) ourTail tailMap,
                   subEdges) --Means we are a leaf node, no sub-expressions
         _ ->  (trace "In fallthrough version of getEdges" ) $ do
           --TODO need each sub-exp?
           let subExprs = (directSubExprs e) :: [LabeledExpr]
           let subHeads = trace ("Sub Expressions: " ++ show subExprs ) $ map (\ex -> headMap `mapGet` (getLabel ex)) subExprs
           let subTails = map (\ex -> tailMap `mapGet` (getLabel ex)) subExprs
           let ourHead = trace ("Sub heads " ++ show subHeads ++ "\nsub tails " ++ show subTails) $ head subHeads
           let ourTail = trace ("Sub edges " ++ show subEdges ) $ last subTails
           let subExpEdges = concatMap connectLists $ zip (init subTails) (tail subHeads)
           return (Map.insert (getLabel e) ourHead headMap
                 , Map.insert (getLabel e) ourTail tailMap
                  --, subNodes
                  , subEdges ++ subExpEdges)  --Arithmetic doesn't need its own statements, since we can do inline
      False -> oneLevelEdges fnInfo (binOpToFn e) maybeSubInfo
    --Data _ args -> paramNodes args --Ctor is a constant, so just evaluate the arguments
    MultiIf condCasePairs -> do
      --We treat each case of the if expression as an assignment to the final value
      --of the if expression
      let guards = (map fst condCasePairs)
      let bodies = map snd condCasePairs
      let bodyTails = concatMap tailExprs bodies
      --let guardNodes = map Branch guards
      let bodyNodes = map (tailAssign $ getLabel e) bodyTails
      --Each guard is connected to the next guard, and the "head" control node of its body
      let ourHead = headMap `mapGet` (getLabel $ head guards)
      let otherHeads = map (\arg -> headMap `mapGet` (getLabel $ arg) ) (tail guards)
      let guardEnds = map (\arg -> tailMap `mapGet` (getLabel $ arg) ) guards
      let notLastGuardEnds = init guardEnds
      let bodyHeads = map (\arg -> headMap `mapGet` (getLabel $ arg) ) bodies

      let guardFallthroughEdges = concatMap connectLists $ zip notLastGuardEnds otherHeads
      let guardBodyEdges = concatMap connectLists $ zip guardEnds bodyHeads

      let ourTail = [(Assign (IntermedExpr (getLabel e)) body) | body <- bodies]
      let endEdges = connectLists (bodyNodes, ourTail)

      return (
        Map.insert (getLabel e) ourHead headMap --First statement is eval first guard
         ,Map.insert (getLabel e) ourTail tailMap --Last statements are any tail exps of bodies
        --,guardNodes ++ bodyNodes ++ subNodes
         ,subEdges ++ guardBodyEdges ++ guardFallthroughEdges  ++ endEdges)
    Case caseExpr patCasePairs -> do
      --We treat each case of the case expression as an assignment to the final value
      --of the case expression
      --Those assignments correspond to the expressions in tail-position of the case
      let cases = map snd patCasePairs
      let caseTailExprs = concatMap tailExprs cases
      let caseTails =  map (\tailExpr -> Assign (IntermedExpr $ getLabel e) tailExpr ) caseTailExprs

      let branchNode = Branch e
      --let ourHead = case (headMap `mapGet` (getLabel caseExpr)) of
      --      [] -> [Assign (IntermedExpr $ getLabel caseExpr) caseExpr]
      --      headList -> headList
      let ourHead = headMap `mapGet` (getLabel caseExpr)
      let ourTail = [Assign (IntermedExpr (getLabel e)) theCase | theCase <- caseTailExprs]

      let caseHeads = concatMap (\cs -> headMap `mapGet` (getLabel cs) ) cases
      let branchEdges = connectLists (ourHead, [branchNode])
      let caseEdges =  connectLists ([branchNode], caseHeads)

      let endEdges = connectLists (caseTails, ourTail)

      return $ (Map.insert (getLabel e) ourHead headMap
        ,Map.insert (getLabel e) ourTail tailMap --Last thing is tail statement of whichever case we take
        --,[Assign (IntermedExpr $ getLabel caseExpr) caseExpr] ++ caseNodes ++ subNodes
         ,subEdges ++ caseEdges ++ endEdges ++ branchEdges)
    Let defs body -> do
      --We treat the body of a let statement as an assignment to the final value of
      --the let statement
      --Those assignments correspond to the expressions in tail-position of the body
      let orderedDefs = defs --TODO sort these
      let getDefAssigns (GenericDef pat b _) = trace "DefAssigns" $ concatMap (varAssign label pat) $ tailExprs b
      let defAssigns = map getDefAssigns orderedDefs
      --let bodyAssigns = map (tailAssign $ getLabel e) $ tailExprs body

      let (ourHead:otherHeads) = map (\(GenericDef _ b _) -> headMap `mapGet` (getLabel b)) orderedDefs

      let lastDefs = map  (\defList->[last defList] ) defAssigns
      let firstDefs = map (\defList->[head defList] ) defAssigns

      --let ourHead = case (head allHeads) of
      --      [] -> head defAssigns
      --      headList -> headList
      --let otherHeads = tail allHeads
      --TODO separate variables?

      let bodyHead = headMap `mapGet` (getLabel body)
      let tailLists = map (tailMap `mapGet`) $ map (\(GenericDef _ rhs _) -> getLabel rhs) orderedDefs

      let bodyTail = tailMap `mapGet` (getLabel body)
      let ourTail = [Assign (IntermedExpr (getLabel e)) body]

      let betweenDefEdges =
            concatMap connectLists $ zip lastDefs (otherHeads ++ [bodyHead])
      let tailToDefEdges = concatMap connectLists $ zip tailLists firstDefs
      let interDefEdges =
            [(d1, d2) | defList <- defAssigns, d1 <- (init defList), d2 <- (tail defList)]
      let assignExprEdges = connectLists (bodyTail, ourTail)

      --TODO need intermediate?

      return $ (Map.insert (getLabel e) ourHead headMap
                ,Map.insert (getLabel e) ourTail tailMap
                --,defAssigns ++ bodyAssigns ++ subNodes
                ,subEdges ++ betweenDefEdges
                 ++ tailToDefEdges ++ interDefEdges ++ assignExprEdges)

    _ -> (trace "Fallthrough" ) $ case (headMaps) of
      [] -> (trace "Leaf case" ) $ do
        
        let ourHead = [ExprEval e]
        let ourTail = ourHead
        return (Map.insert (getLabel e) ourHead headMap,
                Map.insert (getLabel e) ourTail tailMap,
                subEdges) --Means we are a leaf node, no sub-expressions
      _ ->  (trace "In fallthrough version of getEdges" ) $ do
        --TODO need each sub-exp?
        let subExprs = (directSubExprs e) :: [LabeledExpr]
        let subHeads = trace ("Sub Expressions: " ++ show subExprs ) $ map (\ex -> headMap `mapGet` (getLabel ex)) subExprs
        let subTails = map (\ex -> tailMap `mapGet` (getLabel ex)) subExprs
        let ourHead = trace ("Sub heads " ++ show subHeads ++ "\nsub tails " ++ show subTails) $ head subHeads
        let ourTail = trace ("Sub edges " ++ show subEdges ) $ last subTails
        let subExpEdges = concatMap connectLists $ zip (init subTails) (tail subHeads)
        return (Map.insert (getLabel e) ourHead headMap
              , Map.insert (getLabel e) ourTail tailMap
               --, subNodes
               , subEdges ++ subExpEdges) 
        --Other cases don't generate control nodes for one-level analysis
        --For control flow, we just calculate each sub-expression in sequence
        --We connect the end nodes of each sub-expression to the first of the next


allDefEdges
  :: Map.Map Var FunctionInfo
  -> LabelDef
  -> Maybe (
    Map.Map Label [ControlNode],
    Map.Map Label [ControlNode],
    [(ControlNode, ControlNode)] )
allDefEdges fnInfo d@(GenericDef pat body ty) =
  if (isStateMonadFn ty)
  then monadicDefEdges fnInfo d
  else allExprEdges fnInfo $ functionBody body

allExprEdges
  :: Map.Map Var FunctionInfo
  -> LabeledExpr
  -> Maybe (
    Map.Map Label [ControlNode],
    Map.Map Label [ControlNode],
    [(ControlNode, ControlNode)] )
allExprEdges fnInfo e = foldE
           (\ _ () -> repeat ())
           ()
           (\(GenericDef _ e v) -> [e])
           (\ _ e subs-> oneLevelEdges fnInfo e subs)
           e

nameToCanonVar :: String -> Var
nameToCanonVar name = Variable.Canonical  Variable.Local name

functionDefEdges
  :: (Map.Map Label [ControlNode]
    ,Map.Map Label [ControlNode])
  -> LabelDef
  -> Maybe [ControlEdge]
functionDefEdges (headMap, tailMap) (GenericDef (Pattern.Var name) e@(A (_,label,_) _) _ty ) = trace "Getting Function Edges " $ do
  let body = functionBody e
  let argPats = (functionArgPats e)
  let argLabels = (functionArgLabels e)
  let argPatLabels = zip argPats argLabels
  let argVars = concatMap getPatternVars argPats
  let ourHead = ProcEntry e
  let ourTail = [ProcExit e]
  let bodyTails = tailExprs body
  let tailNodes = concatMap (\e -> tailMap `mapGet` (getLabel e) ) bodyTails
  let assignReturns = [AssignParam
                        (FormalReturn (nameToCanonVar name) )
                        (IntermedExpr $ getLabel body) body]
  let assignParams =
        [(AssignParam (FormalParam pat label) (NormalVar v argLab) body) |
           (pat,argLab) <- argPatLabels, v <- getPatternVars pat]
  let (startEdges, assignFormalEdges, gotoBodyEdges) =
        case argPats of
          [] -> (connectLists([ourHead], headMap `mapGet` (getLabel body)),
                [], [])
          _ -> ([(ourHead, head assignParams )],
              zip (init assignParams) (tail assignParams),
              connectLists ([last assignParams], headMap `mapGet` (getLabel body)))
  let assignReturnEdges = connectLists (tailNodes, assignReturns)
  let fnExitEdges = connectLists (assignReturns, ourTail)

  return $ startEdges ++ assignFormalEdges ++ assignReturnEdges ++ fnExitEdges ++ gotoBodyEdges

--Given a monadic expression, break it up into statements
--And calculate the edges between those statements in our CFG
--TODO self recursion
--TODO nested state monads?
monadicDefEdges
  :: Map.Map Var FunctionInfo
  -> LabelDef
  -> Maybe (
    Map.Map Label [ControlNode],
    Map.Map Label [ControlNode],
    [(ControlNode, ControlNode)] )
monadicDefEdges fnInfo (GenericDef (Pattern.Var fnName) e _) =  do
  let body = functionBody e
  let (patternStmts, lastStmt) = sequenceMonadic body
  let allStmts = (map fst (patternStmts)) ++ [lastStmt]
  let patternLabels = map snd patternStmts
  statementNodes <- forM allStmts (allExprEdges fnInfo)

  let linkStatementEdges (stmtInfo1, (pat,andThenExpr), stmtInfo2) = do
        let (s1, (_, tailMap1, _)) = stmtInfo1
        let (s2, (headMap2, _, _)) = stmtInfo2
        let s1Tail = tailMap1 `mapGet` (getLabel s1)
        let s2Head = headMap2 `mapGet` (getLabel s2)
        --TODO is this the right label?
        let assignParamNode = AssignParam (FormalParam pat (getLabel s2)) (IntermedExpr (getLabel s1)) andThenExpr
        return $  (connectLists (s1Tail, [assignParamNode] )) ++ (connectLists ([assignParamNode], s2Head))

  let stmtsAndNodes = zip allStmts statementNodes
  let edgeTriples =  zip3 (init stmtsAndNodes) patternLabels (tail stmtsAndNodes)
  let betweenStatementEdges = concatMap linkStatementEdges edgeTriples
  let combinedHeads = Map.unions $ map (\(hmap,_,_) -> hmap) statementNodes
  let combinedTails = Map.unions $ map (\(_, tmap, _) -> tmap) statementNodes
  let lastStatementTails = combinedTails `mapGet` (getLabel $ lastStmt )
  let ourTails =
        [AssignParam
         (IntermedExpr (getLabel body))
         (IntermedExpr $ getLabel $ lastStmt)
         e]
  let finalAssignEdges = connectLists(lastStatementTails, ourTails)
  let newHeads =
        Map.insert (getLabel body) (combinedHeads `mapGet` (getLabel $ head allStmts)) combinedHeads
  let newTails =
        Map.insert (getLabel body) ourTails combinedTails
  return $ (newHeads,
           newTails,
           finalAssignEdges ++ concat betweenStatementEdges
             ++ concatMap (\(_,_,edges) -> edges) statementNodes)


varAssign :: Label -> Pattern -> LabeledExpr -> [ControlNode]
varAssign defLabel pat e = [Assign (NormalVar pvar defLabel  ) e |
                   pvar <- getPatternVars pat]


functionName :: LabeledExpr -> Maybe Var
functionName (A _ e) = case e of
  Var v -> Just v
  (App f _ ) -> functionName f
  _ -> trace "Error getting fn name" $ Nothing

functionBody :: LabeledExpr -> LabeledExpr
functionBody (A _ (Lambda _ e)) = functionBody e
functionBody e = e

functionLabel (GenericDef _ body _) = case functionBody body of
  (A (_, label, _) _) -> label

functionArgPats :: LabeledExpr -> [Pattern]
functionArgPats (A _ (Lambda pat e)) = [pat] ++ (functionArgPats e)
functionArgPats _ = []

functionArgLabels :: LabeledExpr -> [Label]
functionArgLabels (A (_,l,_) (Lambda pat e)) = [l] ++ (functionArgLabels e)
functionArgLabels _ = []

--Get the "final" return type of a function type
--i.e. what's returned if it is fully applied
functionFinalReturnType :: Type.CanonicalType -> Type.CanonicalType
functionFinalReturnType t@(Type.Lambda _ ret) = trace ("\nFinal Ret "  ++ show ret) $functionFinalReturnType ret
functionFinalReturnType t = t

--Our special State monad for imperative code
stateMonadTycon = Type.Type $ Var.Canonical {Var.home = Var.Module ["State","Escapable"], Var.name = "EState"}

--Check if a function is "monadic" for our state monad
isStateMonadFn :: Maybe Type.CanonicalType -> Bool
isStateMonadFn (Just ty) =  trace ("Checking monad fn " ++ show ty) $ case (functionFinalReturnType ty) of
  (Type.App tyCon _) -> tyCon == stateMonadTycon
  _ -> False
isStateMonadFn _ = trace "monad Nothing Type" $ False

--Given a monadic function, sequence it into a series of "statements"
--Based on the `andThen` bind operator, used in infix position
sequenceMonadic :: LabeledExpr
                -> ([(LabeledExpr, (Pattern,LabeledExpr))]
                    , LabeledExpr)
sequenceMonadic e@(A _ (Binop op e1 (A _ (Lambda pat body)) )) = case (Var.name op) of
  "andThen" -> let
      (bodySeq,bodyTail) = sequenceMonadic body
      newSeq = [(e1, (pat,e))] ++ bodySeq
    in ( newSeq, bodyTail)
  _ -> ([],e)
sequenceMonadic e = ([],e)

--TODO make TailRecursive

getArity :: LabeledExpr -> Int
getArity (A _ (Lambda _ e)) = 1 + (getArity e)
getArity e = 0

tyArity :: Type.CanonicalType -> Int
tyArity (Type.Lambda _ e) = 1 + (tyArity e)
tyArity _ = 0

argsGiven :: LabeledExpr -> Maybe [LabeledExpr]
argsGiven (A _ e) = case e of
  Var v -> Just []
  (App f e ) -> (++[e]) `fmap` argsGiven f
  _ -> trace "Error for args given" $ Nothing

--TODO qualify?
specialFnNames = Set.fromList ["newRef", "deRef", "writeRef", "runState"]

--TODO add module?
isSpecialFn :: Var -> Bool
isSpecialFn v = trace ("!!!! Is Special?" ++ (show $ Var.name v) ) $ Set.member (Var.name v) specialFnNames

specialFnEdges
  :: Map.Map Var FunctionInfo
  -> (Map.Map Label [ControlNode], Map.Map Label [ControlNode])
  -> LabeledExpr
  -> Maybe (Map.Map Label [ControlNode], Map.Map Label [ControlNode], [ControlEdge])
specialFnEdges fnInfo (headMap, tailMap) e@(A _ expr) = do
  fnName <- functionName e
  argList <- argsGiven e
  let firstHead = (headMap `mapGet` (getLabel $ head argList))
  let otherHeads = map (\arg -> headMap `mapGet` (getLabel $ arg) ) $ tail argList
  let tailLists = map (\arg -> tailMap `mapGet` (getLabel $ arg) )  argList
  let argNodes = paramNodes argList
  let assignParamEdges = concatMap connectLists $ zip tailLists argNodes
  let calcNextParamEdges = concatMap connectLists $ zip (init argNodes) otherHeads
  ourTail <- case (Var.name fnName) of
    --We pass on our monadic value by writing to the "value" of the statement
    "newRef" -> return $
      [AssignParam
       (IntermedExpr $ getLabel e)
       (IntermedExpr (getLabel $ head argList))
       e]
    "deRef" -> case (head argList) of
        (A _ (Var ref)) -> return $ [AssignParam (IntermedExpr $ getLabel e) (Ref ref) e]
        _ -> trace ("Error for special edges deRef" ++ show argList ) $ Nothing
    "writeRef" -> case (head argList) of
        (A _ (Var ref)) -> return $ [Assign (Ref ref) e]
        _ -> trace ("Error for special edges writeRef" ++ show argList ) Nothing
    "runState" -> case argList of
      [A _ (Var e)] -> error "TODO runState"
      [A _ (App e1 _)] -> do
         stateFnName <- functionName e1
         return [AssignParam (IntermedExpr $ getLabel e) (FormalReturn stateFnName) e]
      _ -> trace "Error for special edges" $ Nothing
  --TODO connect our tail to the params tail
  let goToTailEdges = connectLists (tailMap `mapGet` (getLabel $ last argList), ourTail)
  return (Map.insert (getLabel e) firstHead headMap,
          Map.insert (getLabel e) ourTail tailMap,
          assignParamEdges ++ calcNextParamEdges ++ goToTailEdges)


isArith :: Var -> Bool
isArith = (`elem` arithVars )

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


interfaceFnInfo :: Map.Map Name PublicModule.Interface -> Map.Map Var FunctionInfo
interfaceFnInfo interfaces = let
    nameIfaces = Map.toList interfaces
    nameSets = [(extModName, fnName, iface) | (extModName, iface) <- nameIfaces,
                                     (Var.Value fnName) <- Module.iExports iface]
  in Map.fromList $ map (\(extModName, fnName, iface)  -> let
                       fnTy = (Module.iTypes iface) `mapGet` fnName
                       fnArity = tyArity fnTy
                       (Name modStrings) = extModName
                       varName = Var.Canonical (Var.Module modStrings) fnName
                       fParams = map (\n -> ExternalParam n varName) [1 .. fnArity]
                     in (varName, FunctionInfo {
                       arity = fnArity,
                       formalParams = fParams, -- [VarPlus],
                       entryNode = ExternalCall varName fParams, -- :: ControlNode,
                       exitNode = ExternalCall varName fParams, -- :: ControlNode,
                       topFnLabel = Nothing })) nameSets
