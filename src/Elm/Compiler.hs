{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
module Elm.Compiler
    ( version
    , parseDependencies, compile, optAndPrint, basicIface, testCompile
    ) where

import Control.Monad.Error (MonadError, throwError)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Text.PrettyPrint as P

import qualified AST.Module as Module
import qualified Compile
import qualified Elm.Compiler.Module as PublicModule
import qualified Elm.Compiler.Version as Version
import Elm.Utils ((|>))
import qualified Generate.JavaScript as JS
import qualified Parse.Helpers as Help
import qualified Parse.Module as Parse

import AST.PrettyPrint (pretty)

import Optimize.Optimize (optimizeModule)

import Language.Elm.CoreSources

import Debug.Trace (trace)

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
compile user packageName source interfaces =
  let unwrappedInterfaces =
        Map.mapKeysMonotonic (\(PublicModule.Name name) -> name) interfaces
  in
      case Compile.compile user packageName unwrappedInterfaces source of
        Right modul -> do
            (modName, _) <- parseDependencies source
            let iface = Module.toInterface modul
            let (optimizedModul, optIface) = optimizeModule modName (modul, iface)
            Right (optIface, JS.generate optimizedModul)

        Left docs ->
            map P.render docs
              |> List.intersperse ""
              |> unlines
              |> Left


{-| Optimize then PrettyPrint Elm code -}
optAndPrint
    :: String
    -> Either String String
optAndPrint source = case Compile.compile "elm-lang" "core" unwrappedBasic source  of
        Right modul -> do
            (modName, _) <- parseDependencies source
            let iface = Module.toInterface modul
            let (optimizedModul, optIface) = optimizeModule modName (modul, iface)
            let body = Module.body optimizedModul
            let expr = Module.program $ body
            Right $ P.render $ pretty expr

        Left docs ->
            map P.render docs
              |> List.intersperse ""
              |> unlines
              |> Left

testCompile src =
  case (compile "elm-lang" "core" src basicIface ) of
    Right (_, js) -> js
    Left docs -> error $ "Failed during compiling" ++  (show  docs)

fromRight (Right x ) = x
fromRight _ = error "Can't unwrap Right from Left"

fromName (PublicModule.Name s) = s

unwrappedBasic :: (Map.Map [String] PublicModule.Interface)
unwrappedBasic = let
    depList = map (fromRight . parseDependencies) stdlibSources
    nameList = zip (map fst depList) stdlibSources
    sourceDict = Map.fromList nameList
    result = compile "elm-lang" "core"
      (sourceDict Map.! (PublicModule.Name ["Basics"]) ) (Map.empty)
    iface = case result of
      Left docs -> error $ "Failed making basics "
      Right (x, _) -> x
  in trace ("Iface" ++ show iface) $ Map.fromList [( ["Basics"], iface)]

basicIface :: (Map.Map PublicModule.Name PublicModule.Interface)
basicIface = let
    depList = map (fromRight . parseDependencies) stdlibSources
    nameList = zip (map fst depList) stdlibSources
    sourceDict = Map.fromList nameList
    result = compile "elm-lang" "core"
      (sourceDict Map.! (PublicModule.Name ["Basics"]) ) (Map.empty)
    iface = case result of
      Left docs -> error $ "Failed making basics "
      Right (x, _) -> x
  in Map.fromList [( PublicModule.Name ["Basics"], iface)] 
