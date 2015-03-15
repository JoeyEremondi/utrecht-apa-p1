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


{-
liftJoin
  :: Lattice payload
  -> (EmbPayload d payload)
  -> (EmbPayload d payload)
  -> (EmbPayload d payload)
liftJoin lat = \(EmbPayload domain1 x) (EmbPayload domain2 y) ->
  EmbPayload (domain1 ++ domain2) $ \ d -> (latticeJoin lat) (x d) (y d)
-}

fnEquality
  :: (Eq payload, Show payload, Show d)
  => EmbPayload d payload
  -> EmbPayload d payload -> Bool
fnEquality lh1@(EmbPayload (domain, lhat)) lh2@(EmbPayload (_, lhat')) =
  let
    areEq = (map ( lhat $ ) domain) == (map (lhat' $ ) domain)
  in areEq

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

naiveLift :: (label -> payload -> payload) -> (label -> ( d -> payload) -> (d -> payload))
naiveLift f lab lhat = (f lab) . lhat

liftToFn
  :: Int
  -> Lattice (payload) --Our embellished lattice
  -> (Map.HashMap LabelNode payload -> LabelNode -> payload -> payload) --Original transfer function
  -> ((LabelNode, LabelNode) -> (payload, payload) -> payload) --special 2-value return function
  -> Map.HashMap LabelNode (EmbPayload LabelNode payload)
  -> LabelNode
  -> (EmbPayload LabelNode payload)
  -> (EmbPayload LabelNode payload)

liftToFn depth lat@Lattice{..} f  _fret _resultMap (Call label) (EmbPayload (domain, lhat)) =
  EmbPayload (domain, \d -> case d of
    [] -> latticeBottom
    ( lc:dRest) -> let
          isGoodEnd ldom = (take depth (lc:ldom)) == (lc:dRest)
          possibleEnds = filter isGoodEnd domain
        in if (Call label == lc)
           then joinAll lat [lhat dPoss | dPoss <- possibleEnds]
           else joinAll lat [lhat dPoss | dPoss <- possibleEnds]) --error "Invalid call string"
liftToFn _ _ _f fret resultMap rnode@(Return _ label) (EmbPayload (domain, lhat')) =
  let
    (EmbPayload (_, lhat)) = (resultMap Map.! (Call label) )
  in EmbPayload (domain,
                 \d -> --We assume they have the same domain
                   fret (Call label, rnode)  (lhat d, lhat' ((Call label):d) ) )
liftToFn _ _ f _ resultMap lnode (EmbPayload (domain, lhat)) = let
    simpleMap = (error "Shouldn't use resultMap in non lifted this case" )
  in EmbPayload (domain ,\d -> (f simpleMap lnode) (lhat d))

--TODO need reverse graph?
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
  in callMap

contextDomain :: [Label] -> Int -> Map.HashMap Label [Label] -> [[Label]]
contextDomain allLabels n callMap = helper n callMap ([[]] ++ map (\x -> [x]) allLabels)
  where
    helper 0 _ _ = [[]]
    helper 1 _ accum = accum
    helper n callMap accum = let
        oneLevelPaths = [ (l2:l1:callStr) |
                         (l1:callStr) <- accum,
                         l2 <- (callMap Map.! l1)]
        newAccum = List.nub $ accum ++ oneLevelPaths
      in helper (n-1) callMap newAccum
