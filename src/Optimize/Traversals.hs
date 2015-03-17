{-Joseph Eremondi UU# 4229924
  Utrecht University, APA 2015
  Project one: dataflow analysis
  March 17, 2015 -}

{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}


{-|
Traversals, transformations and folds for expressions,
meant to be as generic as possible with regard to their
annotations and variable types.

The functions here are used to add information to expressions
that is necessary for optimizing.
|-}
module Optimize.Traversals where

import           Optimize.Environment

import           AST.Annotation           (Annotated (A))
import qualified AST.Expression.Canonical as Canon
import           AST.Expression.General
import qualified AST.Module               as Module
import qualified AST.Pattern              as Pattern
import qualified AST.Type                 as Type
import qualified AST.Variable             as Var
import qualified Data.IntMap              as IntMap
import qualified Data.Map                 as Map

import qualified Data.List                as List


import           Optimize.Types
{-|
Given:
A function producing a new context for each child expression or def
   (this is always safe if the list is infinite)
An initial context, passed to our transforming functions
A tuple of functions which, given a context,
   transform the annotations, definitions, variables, and resulting expression
And an expression to transform
Recursively transform the expression and all its sub-expressions, generating
new contexts with the given function and passing them down as we go.
This is useful for things like numbering all expressions
Or traversing all definitions while keeping an environment
|-}
tformE
  :: (Expr a d v -> context -> [context])
  -> context
  -> (context -> a -> aa,
            context -> d -> dd,
            context -> v -> vv,
            context -> Expr aa dd vv -> Expr aa dd vv)
  -> Expr a d v
  -> Expr aa dd vv
tformE cf ctx f@(fa, _fd, _fv, fe) ea@(A ann e)  = fe ctx $ A (fa ctx ann) (tformEE cf (cf ea ctx) ctx f e)

{- |
Version of tformE that works on un-annotated expressions.
This is where we actually branch on different expression types
|-}
tformEE
  :: (Expr a d v -> context -> [context])
  -> [context]
  -> context
  -> (context -> a -> aa,
            context -> d -> dd,
            context -> v -> vv,
            context -> Expr aa dd vv -> Expr aa dd vv)
  -> Expr' a d v
  -> Expr' aa dd vv
tformEE cf ctxList ctx f@(_fa, fd, fv, _fe) expr = let
    --laziness lets us do this
    --ctxList = cf exp ctx
    ctxTail = tail ctxList
    (ctx1:ctx2:_) = ctxList
    makeCtxPairs l = case l of
      [] -> []
      (c1:c2:cRest) -> (c1,c2):(makeCtxPairs cRest)
    ctxPairs = makeCtxPairs ctxList
  in case expr of
   (Literal l) -> Literal l
   (Var name) -> Var $ fv ctx name
   (Range e1 e2) -> Range (tformE cf ctx1 f e1) (tformE cf ctx2 f e2)
   (ExplicitList exprs) -> ExplicitList $ map (\(c,e) -> tformE cf c f e) $ zip ctxList exprs
   (Binop op e1 e2) -> Binop (fv ctx op) (tformE cf ctx1 f e1) (tformE cf ctx2 f e2)
   (Lambda pat body) -> Lambda (tformP (fv ctx) pat) (tformE cf ctx1 f body)
   (App e1 e2) -> App (tformE cf ctx1 f e1) (tformE cf ctx2 f e2)
   (MultiIf exprs) -> MultiIf $ map (\((c1, c2), (e1, e2)) -> (tformE cf c1 f e1, tformE cf c2 f e2))
                      $ zip ctxPairs exprs
   (Let defs body) -> Let (map (\(c,d) -> fd c d)$ zip ctxTail defs) (tformE cf ctx1 f body)
   (Case e1 cases) -> Case (tformE cf ctx1 f e1) $ map
                      (\(c, (p,e)) -> (tformP (fv ctx) p, tformE cf c f e)) $ zip ctxTail cases
   (Data ctor exprs) -> Data ctor $ map (tformE cf ctx1 f) exprs
   --record cases
   (Access e1 field) -> Access (tformE cf ctx1 f e1) field
   (Remove e1 field) -> Remove (tformE cf ctx1 f e1) field
   (Insert e1 field e2) -> Insert (tformE cf ctx1 f e1) field (tformE cf ctx1 f e2)
   (Modify e1 mods) -> Modify (tformE cf ctx1 f e1) $ map
                       (\(c, (field, e)) -> (field, tformE cf c f e)) $ zip ctxTail mods
   (Record vars) -> Record $ map (\(c,(field, e)) -> (field, tformE cf c f e)) $ zip ctxList vars
   (PortIn s t) -> PortIn s (tformT (fv ctx) t)
   (PortOut s t e) -> PortOut s (tformT (fv ctx) t) $ tformE cf ctx1 f e
   (GLShader s1 s2 ty) -> GLShader s1 s2 ty


--Since we only have 1 type parameter, we can cheat and
--derive the traversals for Patterns and types
deriving instance Functor Pattern.Pattern
deriving instance Functor Type.Type

-- | Recursively apply a transformation on our Variable type to a pattern
-- | For Patterns, there's only one type argument, so we can derive functor
tformP :: (v -> vv) -> Pattern.Pattern v -> Pattern.Pattern vv
tformP  = fmap


-- | Recursively apply a transformation on our Variable type to a type
-- | For Types, there's only one type argument, so we can derive functor
tformT :: (v -> vv) -> Type.Type v -> Type.Type vv
tformT = fmap

{-|
Given a function which maps an expression and a context to a list of contexts
passed to each direct sub-expression,
An initial context,
A function returning the list of direct sub-expressions in a definition,
A function which takes a context, an expression, and a list of results
from its sub expresssion, and combines them into one result for this expression,
and an initial expression,
recursively traverse the tree and fold the results into a single result
|-}
foldE
  ::(Expr a d v -> context -> [context]) --context generator
  -> context --initial context
  -> (d -> [Expr a d v]) --get expressions for definitions
  -> (context -> Expr a d v -> [b] -> b) --function incorporating results from lower levels
  -> Expr a d v --initial expression
  -> b --result
foldE cf ctx fd f ea@(A _ e) = f ctx ea (foldEE (cf ea ctx) cf fd f e)

{- |
Version of foldE that works on un-annotated Expressions
This is where we branch on different expression types.
We generate the contexts for each sub-expression in foldE,
and they're passed to foldEE as an argument.
|-}
foldEE
  :: [context] ->
  (Expr a d v -> context -> [context]) --context generator
  -> (d -> [Expr a d v]) --get expressions for definitions
  -> (context -> Expr a d v -> [b] -> b) --function incorporating results from lower levels
  -> Expr' a d v --initial expression
  -> [b] --result
foldEE ctxList cf fd f rootE = let
    --laziness lets us do this
    --ctxList = cf rootE ctx
    ctxTail = tail ctxList
    (ctx1:ctx2:_) = ctxList
  in case rootE of
    (Range e1 e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (ExplicitList exprs) ->  map (\(c,e) -> foldE cf c fd f e) $ zip ctxList exprs
    (Binop _ e1 e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (Lambda _ body) -> [foldE cf ctx1 fd f body]
    (App e1 e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (MultiIf exprs) ->  concatMap (\(e1, e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]) exprs
    (Let defs body) ->
                       (map (\(c,e) -> foldE cf c fd f e ) $ zip ctxTail (concatMap fd defs))
                       ++ [foldE cf ctx1 fd f body]
    (Case e1 cases) ->  [foldE cf ctx1 fd f e1]
                       ++ (map ( (\(c,e) ->foldE cf c fd f e) ) $ zip ctxTail (map snd cases) )
    (Data _ exprs) ->   map (\(c,e) -> foldE cf c fd f e) $ zip ctxList exprs
   --record cases
    (Access e1 _field) -> [foldE cf ctx1 fd f e1]
    (Remove e1 _field) -> [foldE cf ctx1 fd f e1]
    (Insert e1 _field e2) ->  [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (Modify e1 mods) ->  [foldE cf ctx1 fd f e1]
                        ++ (map ((\(c,e) -> foldE cf c fd f e) ) $ zip ctxTail $ map snd mods)
    (Record vars) ->  map ((\(c,e) -> foldE cf c fd f e) ) $ zip ctxList $ map snd vars
    (PortOut _s _t e) -> [foldE cf ctx1 fd f e]
   --Leaf cases: fold with empty child list
    _ -> []

-- | Given an Expression transformation function,
-- | Apply it to the expressions in a Canonical module
transformModule :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalModule -> Module.CanonicalModule
transformModule f modul = modul {Module.body = newBody}
  where newBody = transformBody f $ Module.body modul

-- | Given an Expression transformation function,
-- | Apply it to the expressions in a Canonical body
transformBody :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalBody -> Module.CanonicalBody
transformBody f body = body {Module.program = newProgram}
  where newProgram = f (Module.program body )



-- | Identity transformation function ignoring context
cid :: context -> a -> a
cid = (\_ x -> x)

-- | Apply an Expression transforming function to all expressions in a Generic Def
tformDef :: (Expr a (GenericDef a v) v -> Expr aa (GenericDef aa vv) vv) -> GenericDef a v -> GenericDef aa vv
tformDef f (GenericDef p e t) = GenericDef p (f e) t

-- | Given a Canonical expression, convert all of its definitions to Generic format
-- | This makes them much easier to work with in optimization
makeGenericDefs :: Canon.Expr -> Expr Region (GenericDef Region Var) Var
makeGenericDefs = tformE
                  (\_ _ -> repeat ())
                  ()
                  (cid, (\_ (Canon.Definition p e t) ->
                          GenericDef p (makeGenericDefs e) t), cid, cid)
{- |
Given an initial list of integers,
assign each expression a unique label by appending a unique integer
onto the label of its parent expression.
This is just used internally during full label generation.
|-}
makeListLabels
  :: [Int]
  -> Expr a (GenericDef a v) v
  -> Expr (a, [Int]) (GenericDef (a,[Int]) v) v
makeListLabels init = tformE
  (\_ (l) -> map (\i -> [i]++l) [1..] )
  (init)
  ( (\c a -> (a,c)), \lab -> tformDef (makeListLabels lab), cid,
    \lab exp -> exp)

{-|
Given an expression, assign a unique integer label to each of its sub-expressions.
The current way this is done is not particularly efficient.
|-}
makeLabels
  :: Expr a (GenericDef a v) v
  -> Expr (a, Label) (GenericDef (a,Label) v) v
makeLabels e =
  let
    listLabeled = makeListLabels [1] e
    allLabels :: [[Int]]
    allLabels = foldE
      (\_ () -> repeat ())
      ()
      (\(GenericDef _ e v) -> [e])
      (\ _ (A (a,c) _) subs -> [c] ++  (concat subs))
      listLabeled
    labelMap = Map.fromList $ zip allLabels [1..]
    switchToInt e = tformE
      (\ _ () -> repeat () )
      ()
      (\_ (a,c) -> (a,  labelMap Map.! c),
        \_ -> tformDef switchToInt,
        cid, cid) e
  in switchToInt listLabeled

{-|
Given an expression with labels added, traverse the tree
And add to each expression an environment, mapping variable names
to the label of the expression where that variable was defined.

This helps us deal with scoping issues during Optimization.
|-}
addScope
  :: Env Label
  -> Expr (a, Label) (GenericDef (a,Label) Var) Var
  -> Expr (a, Label, Env Label) (GenericDef (a, Label, Env Label) Var) Var
addScope startEnv = tformE
           (extendEnv varsForDef (\(A (_,l) _) -> l ) )
           startEnv
           ((\env (a,l) -> (a,l,env)),
            \env d -> tformDef (addScope env) d,
            cid,
            cid)

-- | Get all variables defined in a definition
varsForDef :: GenericDef a Var -> [Var.Canonical]
varsForDef (GenericDef p _e _v) = getPatternVars p

-- | Given an Expression which is the result of Canonicalization
-- | Convert it to a LabeledExpr, with the richer information needed for optimizing
annotateCanonical :: Env Label -> Label -> Canon.Expr -> LabeledExpr
annotateCanonical initEnv _initLabel = (addScope initEnv) . (makeLabels ) . makeGenericDefs

-- | Convert a labeled expression back to a canonical one, so we can generate JS
toCanonical :: LabeledExpr -> Canon.Expr
toCanonical =
  tformE
  (\ _ () -> repeat () )
  ()
  (
    \_env (reg, _, _) -> reg,
    \_env (GenericDef pat e t) -> Canon.Definition pat (toCanonical e) t,
    cid,
    cid
   )

-- | Useful when we apply a bunch of annotations and get nested tuples
--TODO multiple levels deep?
flattenAnn :: Expr ((a,aa),aaa) d v -> Expr (a,aa,aaa) d v
flattenAnn = tformE (\_ _ -> repeat ()) () (\_ ((a,b),c) -> (a,b,c), cid, cid, cid)

-- | Apply some transformation on un-annotated exprs to an annotated one
liftAnn :: (Expr' a d v -> r) -> (Expr a d v -> r)
liftAnn f (A _ e) = f e

-- | Apply a transformation on expressions, leaving annotations the same
tformEverywhere :: (Expr a (GenericDef a v) v -> Expr a (GenericDef a v) v) -> Expr a (GenericDef a v) v -> Expr a (GenericDef a v) v
tformEverywhere f =
  let
    tformDefs = \ _ (GenericDef pat body ty) -> GenericDef pat (tformEverywhere f body) ty

  in tformE
                  (\_ _ -> repeat ())
                  ()
                  (cid, tformDefs, cid, \_ -> f)

-- | Lift a transformation on expressions to each definition in a module
tformModule :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalModule -> Module.CanonicalModule
tformModule f m =
  let
    body = Module.body m
    expr = Module.program $ body
    newBody = body {Module.program = f expr}
  in m {Module.body = newBody} --TODO more cleanup to be done?


{-|
Given a labeled expresssion and a variable name,
return whether or not the expression refers to that varible,
excluding the Right-Hand-Side of Let statements
Useful for Dead Code elimination.
|-}
expContainsVar :: LabeledExpr -> Var -> Bool
expContainsVar fullE@(A _ e) v = case e of
  Let _ body -> expContainsVar body v
  Var theVar -> v == theVar
  _ -> or $ map (\ex -> expContainsVar ex v) $ directSubExprs fullE

{-|
Given a labeled expresssion and a label of an expresion,
return whether that expression is a sub-expression of the given one.
|-}
expContainsLabel :: LabeledExpr -> Label -> Bool
expContainsLabel e lin =
  foldE
  (\_ () -> repeat () )
  ()
  (\(GenericDef _ ed _v) -> [ed])
  (\ _ (A (_,lExp,_) _) subContains ->
    (or subContains) || (lExp == lin ) ) e

-- | We need a dummy value for calls that are not in scope
--externalCallLabel :: Label
--externalCallLabel =  (-9999)

-- | The default annotation given to external calls
-- | We need this to make optimization information about functions
-- | defined in separate modules
--externalCallAnn :: (Region, Label, Env Label)
--externalCallAnn = (error "Should never access external call region",
--                          externalCallLabel,
--                          error "Should never access external call env")

-- | Given a labeled expression, generate the dictionary mapping
-- | labels to the sub-expressions they represent
labelDict :: LabeledExpr -> IntMap.IntMap LabeledExpr
labelDict e = --IntMap.insert externalCallLabel (A externalCallAnn $ Record []) $
  foldE
  (\ _ () -> repeat ())
  ()
  (\(GenericDef _ ed _v) -> [ed])
  (\ _ ex@(A (_,lExp,_) _) subDicts ->
    IntMap.insert lExp ex $ IntMap.unions subDicts) e


{-|
Given an expresssion representing an entire module,
convert it into a list of top-level definitions.
Useful because of the "nested-definition" format
that Canonicalize uses.
|-}
defsFromModuleExpr :: LabeledExpr -> [LabelDef]
defsFromModuleExpr e = helper e []
  where helper ex accum = case ex of
          (A _ (Let defs body)) -> helper body (defs ++ accum)
          _ -> accum

{-|
Given an expression representing a module (the result of Canonicalize),
and the parameters for a transformation of that expression,
apply it in sequence to each top-level definition of the module.
|-}
tformModE
  :: (Expr a (GenericDef a v) v -> context -> [context])
  -> context
  -> (context -> a -> a,
  context -> GenericDef a v -> GenericDef a v,
  context -> v -> v,
  context -> Expr a (GenericDef a v) v -> Expr a (GenericDef a v) v)
  -> Annotated ann (Expr' ann (GenericDef a v) var)
  -> Expr ann (GenericDef a v) var
tformModE cf c fns e = case e of
  (A ann (Let defs rest)) -> let
      newDefs =
        map (\(GenericDef pat body ty) -> let
                newBody = tformE cf c fns body
             in (GenericDef pat newBody ty)) defs
      newRest = tformModE cf c fns rest
    in A ann $ Let newDefs newRest
  _ -> e

-- | Transform a module, leaving annotation unchanged
tformModEverywhere
  :: (Expr a (GenericDef a v) v -> Expr a (GenericDef a v) v)
  -> Annotated ann (Expr' ann (GenericDef a v) var)
  -> Expr ann (GenericDef a v) var
tformModEverywhere f e =
  let
    tformDefs = \ _ (GenericDef pat body ty) -> GenericDef pat (tformEverywhere f body) ty
  in tformModE (\_ _ -> repeat ()) ()
  (cid,
   tformDefs, --TODO redundant?
   cid,
     \_ -> f)
    e

-- | Given an expression, return the list of expressions it directly references
-- | Should be reasonably efficient due to lazy evaluation
directSubExprs :: LabeledExpr -> [LabeledExpr]
directSubExprs e = snd $ foldE
                 (\_ () -> repeat ())
                 ()
                 (\(GenericDef _ ex _v) -> [ex])
                 (\_ ex subs -> (ex,map fst subs) ) e

