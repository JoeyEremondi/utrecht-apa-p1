{-# LANGUAGE StandaloneDeriving #-}
module Optimize.Types where

import qualified AST.Pattern as Pattern
import qualified AST.Expression.Canonical as Canon
import AST.Type as CanonicalType
import AST.Expression.General
import qualified AST.Annotation as Annotate
import qualified AST.Variable as Var
import qualified Data.Map as Map
import qualified Elm.Compiler.Module as PublicModule


--Generic place to put types and definitions
--To avoid dep cycles


type WholeProgOptFun = 
  [PublicModule.Name] 
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface) 

type ModuleOptFun = PublicModule.Name
                    -> (PublicModule.Module, PublicModule.Interface)
                    -> (PublicModule.Module, PublicModule.Interface)

--Export from AST so that things are nice and encapsulated
type Region = Annotate.Region

type Var = Var.Canonical

type Pattern = Pattern.CanonicalPattern

--Environment types
--We use maps to store what variables are and aren't in scope at a given level
--And the label of the expression in which they were declared
--We never store values for the variables, so we can just use sets
--These environments will often be used as "context" for tree traversals
type Env l = (Map.Map (Var ) l)

type CanonEnv = Env Var.Canonical


data GenericDef a v = GenericDef {
  defPat :: Pattern,
  defBody :: (Expr a (GenericDef a v) v),
  defType:: (Maybe CanonicalType) }
                

--TODO move to better place
newtype Label = Label [Int]
  deriving (Eq, Ord, Show)

type AExpr a = Expr a (GenericDef a Var) Var
type AExpr' a = Expr' a (GenericDef a Var) Var

type LabeledExpr = AExpr (Region, Label, Env Label)
type LabeledExpr' = AExpr' (Region, Label, Env Label)
                        
--Basic getter for labels
label :: LabeledExpr -> Label
label (Annotate.A (_,a,_) _) = a
