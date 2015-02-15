module Optimize.ForwardSlicing (removeDeadCodeWP, removeDeadCodeModule) where

import Elm.Compiler.Module
import qualified Data.Map as Map

removeDeadCodeWP :: [Name] 
  -> Map.Map Name (Module, Interface)
  -> Map.Map Name (Module, Interface) 
removeDeadCodeWP _ m = m --TODO implement


removeDeadCodeModule :: Name -> (Module, Interface) -> (Module, Interface)
removeDeadCodeModule n m = m --TODO
