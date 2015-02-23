module Optimize.Optimize where

import Optimize.Traversals
import qualified AST.Expression.Canonical as Canon
import qualified AST.Module as Module
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Elm.Compiler.Module as PublicModule
import qualified AST.Variable as Var

import qualified Optimize.Reachability as Reachability
--import qualified Optimize.RelevantDefs as RelevantDefs

type WholeProgOptFun = 
  [PublicModule.Name] 
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface) 

type ModuleOptFun = PublicModule.Name
                    -> (PublicModule.Module, PublicModule.Interface)
                    -> (PublicModule.Module, PublicModule.Interface)

{-|
Apply a list of transformations to our canonical ASTs.
The resulting Canonical AST is passed to the generator.
|-}
optimizeProgram :: WholeProgOptFun 
optimizeProgram targets initialModules = foldr (\f modDict ->
                                            f targets modDict) initialModules wholeProgOpts

optimizeModule :: ModuleOptFun
optimizeModule name initialMod =  foldr (\f modDict -> f name modDict) initialMod  moduleOpts


wholeProgOpts :: [WholeProgOptFun]
wholeProgOpts = [Reachability.removeUnreachable
                 --, RelevantDefs.removeDeadCodeWP
          ]

moduleOpts :: [ModuleOptFun]
moduleOpts = [Reachability.removeUnreachableModule
             --, RelevantDefs.removeDeadCodeModule
             ]
