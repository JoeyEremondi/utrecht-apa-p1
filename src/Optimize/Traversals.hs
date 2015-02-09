module Traversals where

import  AST.Expression.General
import AST.Annotation
import AST.Type (CanonicalType)
import qualified AST.Pattern as Pattern
import qualified AST.Expression.Canonical as Canon
import qualified AST.Variable as Var

--Annotated expression types
type AExpr ann = Expr ann (ADef ann) Var.Canonical
type AExpr' ann = Expr' ann (ADef ann) Var.Canonical

data ADef ann = Definition Pattern.CanonicalPattern (AExpr ann) (Maybe CanonicalType)
    deriving (Show)

mapE :: (a -> b) -> AExpr a -> AExpr b
mapE f (A ann e) = A (f ann) (mapEE f e)

mapEE :: (a -> b) -> AExpr' a -> AExpr' b
mapEE _ (Literal l) = Literal l
mapEE _ (Var name) = Var name
mapEE f (Range e1 e2) = Range (mapE f e1) (mapE f e2)
mapEE f (ExplicitList exprs) = ExplicitList $ map (mapE f) exprs
mapEE f (Binop op e1 e2) = Binop op (mapE f e1) (mapE f e2)
mapEE f (Lambda pat body) = Lambda pat (mapE f body)
mapEE f (App e1 e2) = App (mapE f e1) (mapE f e2)
mapEE f (MultiIf exprs) = MultiIf $ map (\(e1, e2) -> (mapE f e1, mapE f e2)) exprs
mapEE f (Let defs body) = Let (map (mapD f) defs) (mapE f body)
mapEE f (Case e1 cases) = Case (mapE f e1) (map (\(p,e) -> (p, mapE f e)) cases)
mapEE f (Data ctor exprs) = Data ctor $ map (mapE f) exprs
--record cases
mapEE f (Access e1 field) = Access (mapE f e1) field
mapEE f (Remove e1 field) = Remove (mapE f e1) field
mapEE f (Insert e1 field e2) = Insert (mapE f e1) field (mapE f e2)
mapEE f (Modify e1 mods) = Modify (mapE f e1) $ map (\(field, e) -> (field, mapE f e)) mods
mapEE f (Record vars) = Record $ map (\(field, e) -> (field, mapE f e)) vars
mapEE _ (PortIn s t) = PortIn s t
mapEE f (PortOut s t e) = PortOut s t $ mapE f e
mapEE _ (GLShader s1 s2 ty) = GLShader s1 s2 ty

mapD :: (a -> b) -> ADef a -> ADef b
mapD f (Definition pat (A ann e) ty) = Definition pat (A (f ann) (mapEE f e)) ty

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

--Apply a transformation recursively, bottom up
tformE :: (AExpr' a -> AExpr' a) -> AExpr a -> AExpr a
tformE f (A ann e) = A ann (f $ tformEE f e)

tformEE :: (AExpr' a -> AExpr' a) -> AExpr' a -> AExpr' a
tformEE f (Literal l) = Literal l
tformEE f (Var name) = Var name
tformEE f (Range e1 e2) = Range (tformE f e1) (tformE f e2)
tformEE f (ExplicitList exprs) = ExplicitList $ map (tformE f) exprs
tformEE f (Binop op e1 e2) = Binop op (tformE f e1) (tformE f e2)
tformEE f (Lambda pat body) = Lambda pat (tformE f body)
tformEE f (App e1 e2) = App (tformE f e1) (tformE f e2)
tformEE f (MultiIf exprs) = MultiIf $ map (\(e1, e2) -> (tformE f e1, tformE f e2)) exprs
tformEE f (Let defs body) = Let (map (tformD f) defs) (tformE f body)
tformEE f (Case e1 cases) = Case (tformE f e1) (map (\(p,e) -> (p, tformE f e)) cases)
tformEE f (Data ctor exprs) = Data ctor $ map (tformE f) exprs
--record cases
tformEE f (Access e1 field) = Access (tformE f e1) field
tformEE f (Remove e1 field) = Remove (tformE f e1) field
tformEE f (Insert e1 field e2) = Insert (tformE f e1) field (tformE f e2)
tformEE f (Modify e1 mods) = Modify (tformE f e1) $ map (\(field, e) -> (field, tformE f e)) mods
tformEE f (Record vars) = Record $ map (\(field, e) -> (field, tformE f e)) vars
tformEE f (PortIn s t) = PortIn s t
tformEE f (PortOut s t e) = PortOut s t $ tformE f e
tformEE f (GLShader s1 s2 ty) = GLShader s1 s2 ty

tformD :: (AExpr' a -> AExpr' a) -> ADef a -> ADef a
tformD f (Definition pat (A ann e) ty) = Definition pat (A ann (tformEE f e)) ty

{-
mapE f (A ann (Literal e)) = A (f ann) (Literal e)
mapE f (A ann (Var e)) = A (f ann) (Var e)
mapE f (A ann (Range e1 e2)) = A (f ann) (Range (mapE f e1) (mapE f e2))
mapE f (A ann (ExplicitList el)) = A (f ann) (ExplicitList $ map (mapE f) el)
mapE f (A ann (Binop var e1 e2)) = A (f ann) (Binop var (mapE f e1) (mapE f e2))
mapE f (A ann (Lambda vars body)) = A (f ann) (Lambda vars $ mapE f body)
mapE f (A ann (App e1 e2)) = A (f ann) (App (mapE f e1) (mapE f e2))
mapE f (A ann (MultiIf es)) = A (f ann) (MultiIf $ map (\(g,e) -> (mapE f g, mapE f e)) es)
mapE f (A ann (Let defs body)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Case e1 e2)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Data e1 e2)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Access e1 e2)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Remove e1 e2)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Insert e1 e2 e3)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Modify e1 e2)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (Record e)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (PortIn e1 e2)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (PortOut e1 e2 e3)) = A (f ann) (_mapAnnotation_body)
mapE f (A ann (GLShader e1 e2 e3)) = A (f ann) (_mapAnnotation_body)

-}
