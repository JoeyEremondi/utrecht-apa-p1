module Optimize.Optimize where


import qualified Optimize.Reachability    as Reachability
import qualified Optimize.SDG             as SDG
import           Optimize.Types



{-
optimizeProgram :: WholeProgOptFun
optimizeProgram targets initialModules = foldr (\f modDict ->
                                            f targets modDict) initialModules wholeProgOpts


wholeProgOpts :: [WholeProgOptFun]
wholeProgOpts = [Reachability.removeUnreachable
                 --,
          ]
-}

{-|
Apply a list of transformations to our canonical ASTs.
The resulting Canonical AST is passed to the JS generator.
|-}
optimizeModule :: ModuleOptFun
optimizeModule ifaces name initialMod =  foldr (\f modDict -> f ifaces name modDict) initialMod  moduleOpts


{-|
The list of optimization functions that we apply, in order
|-}
moduleOpts :: [ModuleOptFun]
moduleOpts = [ --Reachability.removeUnreachableModule
             SDG.removeModuleDeadCode
             ]
