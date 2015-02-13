module Optimize.Optimize where

import Optimize.Traversals
import qualified AST.Expression.Canonical as Canon
import qualified AST.Module as Module
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Elm.Compiler.Module as PublicModule
import qualified AST.Variable as Var

import qualified Optimize.Reachability as Reachability

type OptFun = 
  [PublicModule.Name] 
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface) 

{-|
Apply a list of transformations to our canonical ASTs.
The resulting Canonical AST is passed to the generator.
|-}
optimize :: OptFun 
optimize targets initialModules = foldr (\f modDict ->
                                            f targets modDict) initialModules allOpts


allOpts :: [OptFun]
allOpts = [Reachability.removeUnreachable
          ]



