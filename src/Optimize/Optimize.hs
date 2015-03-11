module Optimize.Optimize where

import Optimize.Traversals
import qualified AST.Expression.Canonical as Canon
import qualified AST.Module as Module
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Elm.Compiler.Module as PublicModule
import qualified AST.Variable as Var

import qualified Optimize.Reachability as Reachability
import qualified Optimize.SDG as SDG
import Optimize.Types



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
                 --,
          ]

moduleOpts :: [ModuleOptFun]
moduleOpts = [ Reachability.removeUnreachableModule
             ,SDG.removeModuleDeadCode
             ]
