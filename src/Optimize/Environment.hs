module Optimize.Environment where

import qualified Data.Map as Map
import AST.Expression.General
import AST.Annotation
import qualified AST.Pattern as Pattern
import Elm.Compiler.Module
import qualified AST.Variable as Var
import qualified Data.List as List

--We use maps to store what variables are and aren't in scope at a given level
--And the label of the expression in which they were declared
--We never store values for the variables, so we can just use sets
--These environments will often be used as "context" for tree traversals
type Env l = (Map.Map (Var.Canonical ) l)

type CanonEnv = Env Var.Canonical

makeLocal :: String -> Var.Canonical
makeLocal s = Var.Canonical (Var.Local) s

addContext :: Name -> Var.Canonical -> Var.Canonical
addContext (Name modList) (Var.Canonical Var.Local name) = Var.Canonical (Var.Module modList) name
addContext _ v = v

nameToVar :: Name -> Var.Canonical
nameToVar (Name lReversed) = case l of
  [n] -> Var.Canonical Var.Local n
  (n:reversedPath) -> Var.Canonical (Var.Module $ reverse reversedPath) n
  where l = reverse lReversed
        
getPatternVars :: Pattern.CanonicalPattern  -> [Var.Canonical]
getPatternVars (Pattern.Data _ pats) = concatMap getPatternVars pats
getPatternVars (Pattern.Record strs) = map makeLocal strs --TODO check this case
getPatternVars (Pattern.Alias s p) = [makeLocal s] ++ (getPatternVars p) --TODO check this case
getPatternVars (Pattern.Var s) = [makeLocal s]
getPatternVars Pattern.Anything = []
getPatternVars (Pattern.Literal _) = []

extendEnv
  :: (Ord l)
  => (d -> [Var.Canonical])
  -> (Expr a d Var.Canonical -> l)
  -> Expr a d Var.Canonical
  -> Env l
  -> [Env l]
extendEnv getDefined getLabel expr env = case expr of
  A ann (Let defs _body) ->
    repeat $ Map.union env $ Map.fromList $ [(v, label) | v <- concatMap getDefined defs]
  A ann (Lambda pat body) ->
    repeat $ Map.union env $ Map.fromList $ [(v, label) | v <- getPatternVars pat]
  _ -> repeat env
  where label = getLabel expr
