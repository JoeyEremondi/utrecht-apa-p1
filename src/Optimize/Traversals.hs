{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
module Optimize.Traversals where

import  AST.Expression.General
import AST.Annotation
import AST.Type (CanonicalType)
import qualified AST.Pattern as Pattern
import qualified AST.Expression.Canonical as Canon
import qualified AST.Variable as Var
import qualified AST.Type as Type
import qualified AST.Module as Module


tformE ::  (a -> aa, d -> dd, v -> vv, Expr aa dd vv -> Expr aa dd vv)
       -> Expr a d v
       -> Expr aa dd vv
tformE f@(fa, _fd, _fv, fe) (A ann e) = fe $ A (fa ann) (tformEE f e)

tformEE :: (a -> aa, d -> dd, v -> vv, Expr aa dd vv -> Expr aa dd vv)
        -> Expr' a d v
        -> Expr' aa dd vv
tformEE _ (Literal l) = Literal l
tformEE (_,_,fv,_) (Var name) = Var $ fv name
tformEE f (Range e1 e2) = Range (tformE f e1) (tformE f e2)
tformEE f (ExplicitList exprs) = ExplicitList $ map (tformE f) exprs
tformEE f@(_,_,fv,_) (Binop op e1 e2) = Binop (fv op) (tformE f e1) (tformE f e2)
tformEE f@(_,_,fv,_) (Lambda pat body) = Lambda (tformP fv pat) (tformE f body)
tformEE f (App e1 e2) = App (tformE f e1) (tformE f e2)
tformEE f (MultiIf exprs) = MultiIf $ map (\(e1, e2) -> (tformE f e1, tformE f e2)) exprs
tformEE f@(_,fd,_,_) (Let defs body) = Let (map fd defs) (tformE f body)
tformEE f@(_,_,fv,_) (Case e1 cases) = Case (tformE f e1) (map (\(p,e) -> (tformP fv p, tformE f e)) cases)
tformEE f (Data ctor exprs) = Data ctor $ map (tformE f) exprs
--record cases
tformEE f (Access e1 field) = Access (tformE f e1) field
tformEE f (Remove e1 field) = Remove (tformE f e1) field
tformEE f (Insert e1 field e2) = Insert (tformE f e1) field (tformE f e2)
tformEE f (Modify e1 mods) = Modify (tformE f e1) $ map (\(field, e) -> (field, tformE f e)) mods
tformEE f (Record vars) = Record $ map (\(field, e) -> (field, tformE f e)) vars
tformEE (_,_,fv,_) (PortIn s t) = PortIn s (tformT fv t)
tformEE f@(_,_,fv,_) (PortOut s t e) = PortOut s (tformT fv t) $ tformE f e
tformEE _ (GLShader s1 s2 ty) = GLShader s1 s2 ty

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

foldE :: (d -> [Expr a d v]) -> (Expr' a d v -> [b] -> b) -> Expr a d v -> b
foldE fd f (A ann e) = (foldEE fd f e)

foldEE :: (d -> [Expr a d v]) -> (Expr' a d v -> [b] -> b) -> Expr' a d v -> b
foldEE fd f rootE@(Range e1 e2) = f rootE [foldE fd f e1, foldE fd f e2]
foldEE fd f rootE@(ExplicitList exprs) = f rootE $ map (foldE fd f) exprs
foldEE fd f rootE@(Binop op e1 e2) = f rootE [foldE fd f e1, foldE fd f e2]
foldEE fd f rootE@(Lambda pat body) = f rootE [foldE fd f body]
foldEE fd f rootE@(App e1 e2) = f rootE [foldE fd f e1, foldE fd f e2]
foldEE fd f rootE@(MultiIf exprs) = f rootE $ concatMap (\(e1, e2) -> [foldE fd f e1, foldE fd f e2]) exprs
foldEE fd f rootE@(Let defs body) = f rootE $ (map (foldE fd f) (concatMap fd defs)) ++ [foldE fd f body]
foldEE fd f rootE@(Case e1 cases) = f rootE $ [foldE fd f e1] ++ (map ( (foldE fd f) . snd ) cases)
foldEE fd f rootE@(Data ctor exprs) = f rootE  $ map (foldE fd f) exprs
--record cases
foldEE fd f rootE@(Access e1 field) = f rootE [foldE fd f e1]
foldEE fd f rootE@(Remove e1 field) = f rootE [foldE fd f e1] 
foldEE fd f rootE@(Insert e1 field e2) = f rootE $ [foldE fd f e1, foldE fd f e2]
foldEE fd f rootE@(Modify e1 mods) = f rootE $ [foldE fd f e1] ++ map ((foldE fd f) . snd) mods
foldEE fd f rootE@(Record vars) = f rootE $ map ((foldE fd f) . snd) vars
foldEE fd f rootE@(PortOut s t e) = f rootE [foldE fd f e]
--Leaf cases: fold with empty child list
foldEE fd f e = f e []

--Transform a parsed and typechecked interface
--transformIface :: (Canon.Expr -> Canon.Expr) -> Module.CanonicalModule -> Module.CanonicalModule
--transformIface f iface = Module.toInterface $ 
