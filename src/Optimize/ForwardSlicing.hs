module Optimize.ForwardSlicing (removeDeadCodeWP, removeDeadCodeModule) where

import Elm.Compiler.Module
import qualified Data.Map as Map
import Optimize.Traversals
import qualified AST.Module as Module
import qualified AST.Expression.Canonical as Canon

import Optimize.Types

--Our different types of control nodes
data ControlNode =
  Statement (LabeledExpr)
  | Call (LabeledExpr)
  | Return (LabeledExpr)
  | ProcEntry (LabeledExpr)
  | ProcExit (LabeledExpr)
  | ForcedDependency --Special unique node, connected to everything
  | GlobalEntry --Always the first node
  | GlobalExit --Always the last node


--Generate control-flow edges for a single expression
--We then pass this function to a fold, which collects them
makeEdges :: LabeledExpr -> [ControlNode]
makeEdges = error "TODO implement makeEdges"
    

removeDeadCodeWP :: [Name] 
  -> Map.Map Name (Module, Interface)
  -> Map.Map Name (Module, Interface) 
removeDeadCodeWP _ m = m --TODO implement


removeDeadCodeModule :: Name -> (Module, Interface) -> (Module, Interface)
removeDeadCodeModule n (m,i) =
  let
    newMod = tformModule removeDeadCode m
  in (newMod,i)

removeDeadCode :: Canon.Expr -> Canon.Expr
removeDeadCode e =
  let
    eAnn = annotateCanonical  (Label []) e
  in e --TODO implement
