{-# LANGUAGE StandaloneDeriving, DeriveFunctor, FlexibleInstances #-}
module Optimize.Traversals where

import Optimize.Environment

import  AST.Expression.General
import AST.Annotation (Annotated(A))
import qualified AST.Pattern as Pattern
import qualified AST.Expression.Canonical as Canon
import qualified AST.Variable as Var 
import qualified AST.Type as Type
import qualified AST.Module as Module
import qualified Data.Map as Map
--import qualified AST.Annotation as Annotation

import Optimize.Types

--Given:
--A function producing a new context for each child expression or def
--   (this is always safe if the list is infinite)
--An initial context, passed to our transforming functions
--A tuple of functions which, given a context,
--   transform the annotations, definitions, variables, and resulting expression
--And an expression to transform
--Recursively transform the expression and all its sub-expressions, generating
--new contexts with the given function and passing them down as we go.
--This is useful for things like numbering all expressions
--Or traversing all definitions while keeping an environment
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
tformEE cf ctxList ctx f@(fa, fd, fv, fe) exp = let
    --laziness lets us do this
    --ctxList = cf exp ctx
    ctxTail = tail ctxList
    (ctx1:ctx2:_) = ctxList
  in case exp of
   (Literal l) -> Literal l
   (Var name) -> Var $ fv ctx name
   (Range e1 e2) -> Range (tformE cf ctx1 f e1) (tformE cf ctx2 f e2)
   (ExplicitList exprs) -> ExplicitList $ map (\(c,e) -> tformE cf c f e) $ zip ctxList exprs
   (Binop op e1 e2) -> Binop (fv ctx op) (tformE cf ctx1 f e1) (tformE cf ctx2 f e2)
   (Lambda pat body) -> Lambda (tformP (fv ctx) pat) (tformE cf ctx1 f body)
   (App e1 e2) -> App (tformE cf ctx1 f e1) (tformE cf ctx1 f e2)
   (MultiIf exprs) -> MultiIf $ map (\(c, (e1, e2)) -> (tformE cf c f e1, tformE cf c f e2))
                      $ zip ctxList exprs
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

  
--Transform a pattern
--For these ones, there's only one type argument, so we can derive functor
tformP :: (v -> vv) -> Pattern.Pattern v -> Pattern.Pattern vv
tformP  = fmap

--Since we only have 1 type parameter, we can cheat and
--derive the traversals for Patterns and types
deriving instance Functor Pattern.Pattern
deriving instance Functor Type.Type


tformT :: (v -> vv) -> Type.Type v -> Type.Type vv
tformT = fmap

--mapD :: (a -> b) -> ADef a -> ADef b
--mapD f (Definition pat (A ann e) ty) = Definition pat (A (f ann) (mapEE f e)) ty

foldE
  ::(Expr a d v -> context -> [context]) --context generator
  -> context --initial context
  -> (d -> [Expr a d v]) --get expressions for definitions
  -> (context -> Expr a d v -> [b] -> b) --function incorporating results from lower levels
  -> Expr a d v --initial expression
  -> b --result
foldE cf ctx fd f ea@(A ann e) = f ctx ea (foldEE (cf ea ctx) cf ctx fd f e)

foldEE
  :: [context] ->
  (Expr a d v -> context -> [context]) --context generator
  -> context --initial context
  -> (d -> [Expr a d v]) --get expressions for definitions
  -> (context -> Expr a d v -> [b] -> b) --function incorporating results from lower levels
  -> Expr' a d v --initial expression
  -> [b] --result
foldEE ctxList cf ctx fd f rootE = let
    --laziness lets us do this
    --ctxList = cf rootE ctx
    ctxTail = tail ctxList
    (ctx1:ctx2:_) = ctxList
  in case rootE of
    (Range e1 e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (ExplicitList exprs) ->  map (\(c,e) -> foldE cf c fd f e) $ zip ctxList exprs
    (Binop op e1 e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (Lambda pat body) -> [foldE cf ctx1 fd f body]
    (App e1 e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (MultiIf exprs) ->  concatMap (\(e1, e2) -> [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]) exprs
    (Let defs body) -> 
                       (map (\(c,e) -> foldE cf c fd f e ) $ zip ctxTail (concatMap fd defs))
                       ++ [foldE cf ctx1 fd f body]
    (Case e1 cases) ->  [foldE cf ctx1 fd f e1]
                       ++ (map ( (\(c,e) ->foldE cf c fd f e) ) $ zip ctxTail (map snd cases) )
    (Data ctor exprs) ->   map (\(c,e) -> foldE cf c fd f e) $ zip ctxList exprs
   --record cases
    (Access e1 field) -> [foldE cf ctx1 fd f e1]
    (Remove e1 field) -> [foldE cf ctx1 fd f e1] 
    (Insert e1 field e2) ->  [foldE cf ctx1 fd f e1, foldE cf ctx2 fd f e2]
    (Modify e1 mods) ->  [foldE cf ctx1 fd f e1]
                        ++ (map ((\(c,e) -> foldE cf c fd f e) ) $ zip ctxTail $ map snd mods)
    (Record vars) ->  map ((\(c,e) -> foldE cf c fd f e) ) $ zip ctxList $ map snd vars
    (PortOut s t e) -> [foldE cf ctx1 fd f e]
   --Leaf cases: fold with empty child list
    _ -> []

--Transform a parsed and typechecked interface
transformModule :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalModule -> Module.CanonicalModule
transformModule f modul = modul {Module.body = newBody}
  where newBody = transformBody f $ Module.body modul

transformBody :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalBody -> Module.CanonicalBody
transformBody f body = body {Module.program = newProgram}
  where newProgram = f (Module.program body )



--Identity ignoring context
cid = (\_ x -> x)

tformDef :: (Expr a (GenericDef a v) v -> Expr aa (GenericDef aa vv) vv) -> GenericDef a v -> GenericDef aa vv
tformDef f (GenericDef p e t) = GenericDef p (f e) t

makeGenericDefs :: Canon.Expr -> Expr Region (GenericDef Region Var) Var
makeGenericDefs = tformE
                  (\_ _ -> repeat ())
                  ()
                  (cid, (\_ (Canon.Definition p e t) -> GenericDef p (makeGenericDefs e) t), cid, cid)

makeLabels :: Label -> Expr a (GenericDef a v) v -> Expr (a, Label) (GenericDef (a,Label) v) v
makeLabels init = tformE
  (\_ (Label l) -> map (\i -> Label $ [i]++l) [1..] )
  (init)
  ( (\c a -> (a,c)), \_ -> tformDef (makeLabels init), cid, cid)

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

varsForDef :: GenericDef a Var -> [Var.Canonical]
varsForDef (GenericDef p e v) = getPatternVars p

annotateCanonical :: Env Label -> Label -> Canon.Expr -> LabeledExpr
annotateCanonical initEnv initLabel = (addScope initEnv) . (makeLabels initLabel) . makeGenericDefs 


--Useful when we apply a bunch of annotations and get nested tuples
--TODO multiple levels deep?
flattenAnn :: Expr ((a,aa),aaa) d v -> Expr (a,aa,aaa) d v
flattenAnn = tformE (\_ _ -> repeat ()) () (\_ ((a,b),c) -> (a,b,c), cid, cid, cid)

liftAnn :: (Expr' a d v -> r) -> (Expr a d v -> r)
liftAnn f (A _ e) = f e

tformEverywhere :: (Expr a d v -> Expr a d v) -> Expr a d v -> Expr a d v
tformEverywhere f = tformE
                  (\_ _ -> repeat ())
                  ()
                  (cid, cid, cid, \_ -> f)

tformModule :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalModule -> Module.CanonicalModule
tformModule f m =
  let
    body = Module.body m
    expr = Module.program $ body
    newBody = body {Module.program = f expr}
  in m {Module.body = newBody} --TODO more cleanup to be done?



expContainsVar :: LabeledExpr -> Var -> Bool
expContainsVar e v =
  foldE
  (\_ () -> repeat () )
  ()
  (\(GenericDef _ e v) -> [e])
  (\ _ (A _ expr) subContains ->
    (or subContains) || case expr of
      Var vexp -> v == vexp
      _ -> False) e
  
expContainsLabel :: LabeledExpr -> Label -> Bool
expContainsLabel e lin =
  foldE
  (\_ () -> repeat () )
  ()
  (\(GenericDef _ e v) -> [e])
  (\ _ (A (_,lExp,_) _) subContains ->
    (or subContains) || (lExp == lin ) ) e

labelDict :: LabeledExpr -> Map.Map Label LabeledExpr
labelDict =
  foldE
  (\ _ () -> repeat ())
  ()
  (\(GenericDef _ e v) -> [e])
  (\ _ e@(A (_,lExp,_) _) subDicts ->
    Map.insert lExp e $ Map.unions subDicts)
