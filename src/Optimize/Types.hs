{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
module Optimize.Types where
-- |A central place to put types and definitions
-- | to avoid dep cycles

import qualified AST.Annotation           as Annotate
import           AST.Expression.General
import qualified AST.Pattern              as Pattern
import           AST.Type                 as CanonicalType
import qualified AST.Variable             as Var
import qualified Data.Map                 as Map
import qualified Elm.Compiler.Module      as PublicModule
import           Text.PrettyPrint         as P

import           AST.PrettyPrint




{-
type WholeProgOptFun =
  [PublicModule.Name]
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)
  -> Map.Map PublicModule.Name (PublicModule.Module, PublicModule.Interface)
-}

-- | Generic type for an optimization transformation
type ModuleOptFun = Map.Map PublicModule.Name PublicModule.Interface
                    -> PublicModule.Name
                    -> (PublicModule.Module, PublicModule.Interface)
                    -> (PublicModule.Module, PublicModule.Interface)

-- |Export from AST so that things are nice and encapsulated
type Region = Annotate.Region

type Var = Var.Canonical

type Pattern = Pattern.CanonicalPattern

-- |Environment types
-- |We use maps to store what variables are and aren't in scope at a given level
-- |And the label of the expression in which they were declared
-- |We never store values for the variables, so we can just use sets
-- |These environments will often be used as "context" for tree traversals
type Env l = (Map.Map (Var ) l)

-- | We label each sub-expression in our AST with a unique integer
type Label = Int
--newtype Label = Label Int
--  deriving (Eq, Ord, Show)

-- | Used as the initial value we pass to the fold that labels an AST
startLabel :: Label
startLabel = 1

-- | Generic type for a Canonical expression generated after Type-checking
-- | But with the annotation on expressions left open
type AExpr a = Expr a (GenericDef a Var) Var
type AExpr' a = Expr' a (GenericDef a Var) Var

-- | The main expression type used during optimization
-- | In addition to line-number information, we give each sub-expression
-- | A unique label, and an environment mapping each name to the point it was defined
type LabeledExpr = AExpr (Region, Label, Env Label)
type LabeledExpr' = AExpr' (Region, Label, Env Label)

-- | Basic getter for labels
getLabel :: LabeledExpr -> Label
getLabel (Annotate.A (_,a,_) _) = a


{-|
Generic type for a definition, as in a Let expression.
We need this because the form defined in AST.Expression.General is
too restrictive on the annotation types allowed for expressions.
|-}
data GenericDef a v = GenericDef {
  defPat  :: Pattern,
  defBody :: (Expr a (GenericDef a v) v),
  defType:: (Maybe CanonicalType) }

-- | The main Definition type we use for optimization
type LabelDef = GenericDef (Region, Label, Env Label) Var

-- | We need this to be able to pretty-print annotated ASTs
instance Pretty LabelDef where
  pretty (GenericDef pattern expr maybeTipe) =
      P.vcat [ annotation, definition ]
      where
        definition = pretty pattern <+> P.equals <+> pretty expr
        annotation = case maybeTipe of
                       Nothing -> P.empty
                       Just tipe -> pretty pattern <+> P.colon <+> pretty tipe

deriving instance Show LabelDef
