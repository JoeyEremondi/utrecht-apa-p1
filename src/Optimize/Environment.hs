{-Joseph Eremondi UU# 4229924
  Utrecht University, APA 2015
  Project one: dataflow analysis
  March 17, 2015 -}

module Optimize.Environment where

import           AST.Annotation
import           AST.Expression.General
import qualified AST.Pattern            as Pattern
import qualified AST.Variable           as Var
import qualified Data.Map               as Map hiding ((!))
import           Elm.Compiler.Module
import           Optimize.Types
--import AST.Expression.Canonical as Canon

-- | Convert a raw string into a "local" variable
makeLocal :: String -> Var
makeLocal s = Var.Canonical (Var.Local) s

{-|
Given a name with the module path for a variable, and a variable with no module information,
add the proper module information to that variable
|-}
addContext :: Name -> Var -> Var
addContext (Name modList) (Var.Canonical Var.Local name) = Var.Canonical (Var.Module modList) name
addContext _ v = v

{-|
Useful for converting between Name, which is used in the Public Elm.Compiler interface,
and Var, which is used internally in the AST
|-}
nameToVar :: Name -> Var
nameToVar (Name lReversed) = case l of
  [] -> error "Can't have a name with no name!"
  [n] -> Var.Canonical Var.Local n
  (n:reversedPath) -> Var.Canonical (Var.Module $ reverse reversedPath) n
  where l = reverse lReversed

{-|
Given a pattern i.e. the left hand of a definition, or function argument,
return the list of variables defined by that pattern.
|-}
getPatternVars :: Pattern.CanonicalPattern  -> [Var]
getPatternVars (Pattern.Data _ pats) = concatMap getPatternVars pats
getPatternVars (Pattern.Record strs) = map makeLocal strs --TODO check this case
getPatternVars (Pattern.Alias s p) = [makeLocal s] ++ (getPatternVars p) --TODO check this case
getPatternVars (Pattern.Var s) = [makeLocal s]
getPatternVars Pattern.Anything = []
getPatternVars (Pattern.Literal _) = []


{-|
Given a function which finds all variables defined in a definition,
A function mapping expressions to our target information type,
an initial expression, and an initial environment,
return an infinite list of environments.

This is used as the "context"-generating function, passing environments
down the AST, in our tree traversals for annotating ASTs.
|-}
extendEnv
  :: (Ord l)
  => (d -> [Var])
  -> (Expr a d Var -> l)
  -> Expr a d Var
  -> Env l
  -> [Env l]
extendEnv getDefined getLabelFn expr env = case expr of
  A _ann (Let defs _body) ->
    repeat $ Map.union env $ Map.fromList $ [(v, label) | v <- concatMap getDefined defs]
  A _ann (Lambda pat _fnBody) ->
    repeat $ Map.union env $ Map.fromList $ [(v, label) | v <- getPatternVars pat]
  _ -> repeat env
  where label = getLabelFn expr

{-|
Given the expression for a module, generate the environment containing only
the top-level "global" definitions for that module.
|-}
--TODO do we need to use list fn from traversals?
globalEnv :: LabeledExpr ->  Env Label
globalEnv expr  =
  let
    (A (_,label,_) (Let defs _)) = expr

  in foldr (\(GenericDef pat _ _) env ->
             foldr (\v newEnv -> Map.insert v label newEnv) env (getPatternVars pat)) Map.empty defs

