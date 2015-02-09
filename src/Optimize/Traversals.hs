module Traversals where

import AST.Expression.General
import AST.Annotation
import qualified AST.Expression.Canonical as Canon
import qualified AST.Variable as Var

mapE :: (a -> b) -> Expr a Canon.Def Var.Canonical -> Expr b Canon.Def Var.Canonical
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

