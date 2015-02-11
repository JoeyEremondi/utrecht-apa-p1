{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
module Elm.Compiler
    ( version
    , parseDependencies, parse, compileModule, compile, optimizeProgram, optimizeLibrary
    ) where

import Control.Monad.Error (MonadError, throwError)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Text.PrettyPrint as P

import qualified AST.Module as Module (HeaderAndImports(HeaderAndImports), toInterface)
import qualified Compile
import qualified Elm.Compiler.Module as PublicModule
import qualified Elm.Compiler.Version as Version
import Elm.Utils ((|>))
import qualified Generate.JavaScript as JS
import qualified Parse.Helpers as Help
import qualified Parse.Module as Parse


-- VERSION

version :: String
version =
    Version.version


-- DEPENDENCIES

parseDependencies
    :: (MonadError String m)
    => String
    -> m (PublicModule.Name, [PublicModule.Name])
parseDependencies src =
    case Help.iParse Parse.headerAndImports src of
        Left msg ->
            throwError (show msg)

        Right (Module.HeaderAndImports names _exports imports) ->
            return
                ( PublicModule.Name names
                , map (PublicModule.Name . fst) imports
                )


-- COMPILATION

{-| Compiles Elm source code to JavaScript. -}
compile
    :: String
    -> String
    -> String
    -> Map.Map PublicModule.Name PublicModule.Interface
    -> Either String (PublicModule.Interface, String)
compile user packageName source interfaces = compileModule `fmap` parse user packageName source interfaces 

compileModule
  :: PublicModule.Module
  -> (PublicModule.Interface, String)
compileModule modul = (Module.toInterface modul, JS.generate modul)

parse
    :: String
    -> String
    -> String
    -> Map.Map PublicModule.Name PublicModule.Interface
    -> Either String PublicModule.Module
parse user packageName source interfaces =
  let unwrappedInterfaces =
        Map.mapKeysMonotonic (\(PublicModule.Name name) -> name) interfaces
  in
      case Compile.compile user packageName unwrappedInterfaces source of
        Right modul ->
            Right modul

        Left docs ->
            map P.render docs
              |> List.intersperse ""
              |> unlines
              |> Left
              

{-| Given interfaces from compiled Elm modules and their compiled JavaScript,
attempt to optimize the given modules, assuming that the program will be run from
the entry point of `main` within the given main module-}              
optimizeProgram
  :: PublicModule.Name 
  -> Map.Map PublicModule.Name (PublicModule.Module, String)
  -> Map.Map PublicModule.Name (PublicModule.Module, String)   
optimizeProgram mainName interfaces = 
  error "TODO implement"
  
{-| Given interfaces from compiled Elm modules and their compiled JavaScript,
attempt to optimize the given modules, assuming that all functions in the given set of modules
must be avaliable as a library, possibly to be called from JavaScrip.
The main purpose of this is to prevent library functions from being marked as "dead code"-}          
optimizeLibrary
  :: Set.Set PublicModule.Name 
  -> Map.Map PublicModule.Name (PublicModule.Module)
  -> Map.Map PublicModule.Name (PublicModule.Module)   
optimizeLibrary targets interfaces = 
  error "TODO implement"
