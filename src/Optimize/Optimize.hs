module Optimize.Optimize where

import Optimize.Traversals
import qualified AST.Expression.Canonical as Canon
import qualified AST.Module as Module
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Elm.Compiler.Module as PublicModule
import qualified AST.Variable as Var

{-|
Apply a list of transformations to our canonical ASTs.
The resulting Canonical AST is passed to the generator.
|-}
optimize
  :: [PublicModule.Name]
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)  
optimize initialAST = error "TODO" --foldr (\f ast -> transformModule f ast) initialAST allOpts


allOpts :: [Canon.Expr -> Canon.Expr]
allOpts = [testOpt]


testOpt = tformE (id, id, id, id)

