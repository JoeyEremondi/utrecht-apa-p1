{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Optimize.EmbellishedMonotone where

import           AST.Annotation             (Annotated (..))
import           AST.Expression.General
import qualified AST.Pattern                as Pattern
import qualified Data.List                  as List
import           Optimize.ControlFlow
import           Optimize.MonotoneFramework
import           Optimize.Traversals
import           Optimize.Types

import qualified Data.Map as NormalMap

import           Debug.Trace                (trace)


import qualified Data.HashMap.Strict                   as Map

newtype EmbPayload a b = EmbPayload ([[a]], ([a] -> b))

instance (Show b, Show a) => Show (EmbPayload a b)
  where
    show (EmbPayload (domain, lhat)) =
      (List.intercalate " ;; " $
        map (\ d -> (show d) ++ " -> " ++ (show $ lhat d)) domain) ++ "\n"

{-|
Given two functions and their finite domains,
determine if they are equal.
|-}
--TODO speed this up?
fnEquality
  :: (Eq payload, Show payload, Show d)
  => EmbPayload d payload
  -> EmbPayload d payload -> Bool
fnEquality lh1@(EmbPayload (domain, lhat)) lh2@(EmbPayload (_, lhat')) =
  let
    areEq = (map ( lhat $ ) domain) == (map (lhat' $ ) domain)
  in  areEq
--trace ("\n\n\nTesting equality of " ++ show (map ( lhat $ ) domain)  ++ "\nand\n" ++ show (map (lhat' $ ) domain)) $

{-|
Given a domain of context-lists,
an extremal lattice value, and a lattice over a payload,
generate an embellished lattice which takes context into account.
|-}
liftToEmbellished
  :: (Eq payload, Show payload, Show d)
  => [[d]]
  -> payload
  -> Lattice payload
  -> Lattice (EmbPayload d payload)
liftToEmbellished domain iotaVal lat =
  let
    embJoin = \ (EmbPayload (_, x)) (EmbPayload (_, y))
                  -> EmbPayload (domain,  \d -> (latticeJoin lat) (x d) (y d))
  in Lattice {
    latticeBottom = EmbPayload (domain,  \_ -> latticeBottom lat),
    latticeJoin = embJoin,
    iota = EmbPayload (domain , \d -> if (null d) then iotaVal else latticeBottom lat),
    lleq = \x y -> fnEquality (embJoin x y) y,
    flowDirection = flowDirection lat
  }

{-|
Given a transfer function, lift it to apply element-wise
to an embellished lattice value.
|-}
naiveLift :: (label -> payload -> payload) -> (label -> ( d -> payload) -> (d -> payload))
naiveLift f lab lhat = (f lab) . lhat

{-|
Given a context-depth, an lattice, a transfer function,
and a special 2-value transfer function for return blocks,
return a transfer function operating on our embellished lattice.

This function manipulates the context strings for Call and Return nodes
to approximate function call strings.
|-}
liftToFn
  :: Int
  -> Lattice (payload) --Our original lattice
  -> (Map.HashMap LabelNode payload -> LabelNode -> payload -> payload) --Original transfer function
  -> ((LabelNode, LabelNode) -> (payload, payload) -> payload) --special 2-value return function
  -> Map.HashMap LabelNode (EmbPayload LabelNode payload)
  -> LabelNode
  -> (EmbPayload LabelNode payload)
  -> (EmbPayload LabelNode payload)

liftToFn depth lat@Lattice{..} f  _fret _resultMap (Call label) (EmbPayload (domain, lhat)) =
  EmbPayload (domain, \d ->  let
          isGoodEnd dposs = (take depth (Call label:dposs)) == d
          possibleEnds = filter isGoodEnd domain
        in 
           joinAll lat [lhat dPoss | dPoss <- possibleEnds])
liftToFn _ _ _f fret resultMap rnode@(Return _ label) (EmbPayload (domain, lhat')) =
  let
    (EmbPayload (_, lhat)) = (resultMap Map.! (Call label) )
  in EmbPayload (domain,
                 \d -> --We assume they have the same domain
                   fret (Call label, rnode)  (lhat d, lhat' ((Call label):d) ) )
liftToFn _ _ f _ resultMap lnode (EmbPayload (domain, lhat)) = let
    simpleMap = (error "Shouldn't use resultMap in non lifted this case" )
  in EmbPayload (domain ,\d -> (f simpleMap lnode) (lhat d))

{-|
Given a module expression, generate a map from each function label
to the list of functions it can directly call.
We use this to generate all possible call strings
of a given length.
|-}
callGraph :: LabeledExpr -> Map.HashMap Label [Label]
callGraph (A _ (Let defs _)) =
  let
    fnNames = map (\(GenericDef (Pattern.Var n) _ _) -> nameToCanonVar n) defs
    fnBodies = map (\(GenericDef _ body _) -> functionBody body ) defs
    fnLabels = map functionLabel defs
    labelDict = NormalMap.fromList $ zip fnNames fnLabels

    oneLevelCalls () expr subCalls = (concat subCalls) ++ case expr of
      (A _ (App (A _ (Var fnName)) _)) ->
        if (NormalMap.member fnName labelDict)
           then [labelDict NormalMap.! fnName]
           else []
      _ -> []

    allCalls = foldE
      (\_ () -> repeat ())
      ()
      (\(GenericDef _ e v) -> [e])
      oneLevelCalls

    callMap = Map.fromList $ zip fnLabels $ map (\body -> allCalls body) fnBodies
    --callMapWithExternal = Map.insert externalCallLabel [] callMap
  in callMap

{-|
Given the set of all labels in a program, a maximum call string length,
and the call-graph for a module,
generate the list of all valid call strings, up to the given length.
|-}
contextDomain :: [Label] -> Int -> Map.HashMap Label [Label] -> [[Label]]
contextDomain allLabels n callMap = helper n callMap ([[]] ++ map (\x -> [x]) allLabels)
  where
    --allLabelsWithExt = [externalCallLabel] ++ allLabels
    helper 0 _ _ = [[]]
    helper 1 _ accum = accum
    helper n callMap accum = let
        oneLevelPaths = [ (l2:l1:callStr) |
                         (l1:callStr) <- accum,
                         l2 <- (callMap Map.! l1)]
        newAccum = List.nub $ accum ++ oneLevelPaths
      in helper (n-1) callMap newAccum
