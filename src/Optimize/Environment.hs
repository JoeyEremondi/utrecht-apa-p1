module Optimize.Environment where

import           AST.Annotation
import           AST.Expression.General
import           AST.Module             (body, program)
import qualified AST.Pattern            as Pattern
import qualified AST.Variable           as Var
import qualified Data.List              as List
import qualified Data.Map               as Map hiding ((!))
import           Elm.Compiler.Module
import           Optimize.Types
--import AST.Expression.Canonical as Canon


makeLocal :: String -> Var
makeLocal s = Var.Canonical (Var.Local) s

addContext :: Name -> Var -> Var
addContext (Name modList) (Var.Canonical Var.Local name) = Var.Canonical (Var.Module modList) name
addContext _ v = v

nameToVar :: Name -> Var
nameToVar (Name lReversed) = case l of
  [n] -> Var.Canonical Var.Local n
  (n:reversedPath) -> Var.Canonical (Var.Module $ reverse reversedPath) n
  where l = reverse lReversed

getPatternVars :: Pattern.CanonicalPattern  -> [Var]
getPatternVars (Pattern.Data _ pats) = concatMap getPatternVars pats
getPatternVars (Pattern.Record strs) = map makeLocal strs --TODO check this case
getPatternVars (Pattern.Alias s p) = [makeLocal s] ++ (getPatternVars p) --TODO check this case
getPatternVars (Pattern.Var s) = [makeLocal s]
getPatternVars Pattern.Anything = []
getPatternVars (Pattern.Literal _) = []

extendEnv
  :: (Ord l)
  => (d -> [Var])
  -> (Expr a d Var -> l)
  -> Expr a d Var
  -> Env l
  -> [Env l]
extendEnv getDefined getLabel expr env = case expr of
  A ann (Let defs _body) ->
    repeat $ Map.union env $ Map.fromList $ [(v, label) | v <- concatMap getDefined defs]
  A ann (Lambda pat body) ->
    repeat $ Map.union env $ Map.fromList $ [(v, label) | v <- getPatternVars pat]
  _ -> repeat env
  where label = getLabel expr

globalEnv :: LabeledExpr ->  Env Label
globalEnv expr  =
  let
    (A (_,label,_) (Let defs _)) = expr

  in foldr (\(GenericDef pat _ _) env ->
             foldr (\v newEnv -> Map.insert v label newEnv) env (getPatternVars pat)) Map.empty defs

