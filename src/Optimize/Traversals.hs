{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
module Traversals where

import  AST.Expression.General
import AST.Annotation
import AST.Type (CanonicalType)
import qualified AST.Pattern as Pattern
import qualified AST.Expression.Canonical as Canon
import qualified AST.Variable as Var
import qualified AST.Type as Type

--Annotated expression types
type AExpr ann = Expr ann (ADef ann) Var.Canonical
type AExpr' ann = Expr' ann (ADef ann) Var.Canonical

data ADef ann = Definition Pattern.CanonicalPattern (AExpr ann) (Maybe CanonicalType)
    deriving (Show)

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

deriving instance Functor Pattern.Pattern
deriving instance Functor Type.Type


tformT :: (v -> vv) -> Type.Type v -> Type.Type vv
tformT = fmap

--mapD :: (a -> b) -> ADef a -> ADef b
--mapD f (Definition pat (A ann e) ty) = Definition pat (A (f ann) (mapEE f e)) ty

foldE :: (AExpr' a -> [b] -> b) -> AExpr a -> b
foldE f (A ann e) = (foldEE f e)

foldEE :: (AExpr' a -> [b] -> b) -> AExpr' a -> b
foldEE f rootE@(Range e1 e2) = f rootE [foldE f e1, foldE f e2]
foldEE f rootE@(ExplicitList exprs) = f rootE $ map (foldE f) exprs
foldEE f rootE@(Binop op e1 e2) = f rootE [foldE f e1, foldE f e2]
foldEE f rootE@(Lambda pat body) = f rootE [foldE f body]
foldEE f rootE@(App e1 e2) = f rootE [foldE f e1, foldE f e2]
foldEE f rootE@(MultiIf exprs) = f rootE $ concatMap (\(e1, e2) -> [foldE f e1, foldE f e2]) exprs
foldEE f rootE@(Let defs body) = f rootE $ (map (foldEInD f) defs) ++ [foldE f body]
foldEE f rootE@(Case e1 cases) = f rootE $ [foldE f e1] ++ (map ( (foldE f) . snd ) cases)
foldEE f rootE@(Data ctor exprs) = f rootE  $ map (foldE f) exprs
--record cases
foldEE f rootE@(Access e1 field) = f rootE [foldE f e1]
foldEE f rootE@(Remove e1 field) = f rootE [foldE f e1] 
foldEE f rootE@(Insert e1 field e2) = f rootE $ [foldE f e1, foldE f e2]
foldEE f rootE@(Modify e1 mods) = f rootE $ [foldE f e1] ++ map ((foldE f) . snd) mods
foldEE f rootE@(Record vars) = f rootE $ map ((foldE f) . snd) vars
foldEE f rootE@(PortOut s t e) = f rootE [foldE f e]
--Leaf cases: fold with empty child list
foldEE f e = f e []

--Fold over expressions within definitions
foldEInD :: (AExpr' a -> [b] -> b) -> ADef a -> b
foldEInD f (Definition pat (A ann e) ty) = foldEE f e 


