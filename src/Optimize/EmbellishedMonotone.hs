{-# LANGUAGE RecordWildCards, ScopedTypeVariables, FlexibleContexts #-}
module Optimize.EmbellishedMonotone where

import Optimize.MonotoneFramework
import Optimize.Types
import Optimize.ControlFlow
import           AST.Annotation             (Annotated (..))
import AST.Expression.General
import qualified AST.Pattern                as Pattern
import Optimize.Traversals
import qualified Data.List as List


import qualified Data.Map as Map

data EmbPayload a b = EmbPayload [[a]] ([a] -> b)

instance (Show b) => Show (EmbPayload a b)
  where
    show (EmbPayload domain lhat) =
      concatMap (\ d -> show $ lhat d) domain
      

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
  :: (Eq payload)
  => EmbPayload d payload
  -> EmbPayload d payload -> Bool
fnEquality (EmbPayload domain lhat) (EmbPayload _ lhat') = (map ( lhat $ ) domain) == (map (lhat' $ ) domain)

liftToEmbellished
  :: (Eq payload)
  => [[d]]
  -> (EmbPayload d payload)
  -> Lattice payload
  -> Lattice (EmbPayload d payload)
liftToEmbellished domain iotaVal lat =
  let
    embJoin = \ (EmbPayload _ x) (EmbPayload _ y)
                  -> EmbPayload domain $ \d -> (latticeJoin lat) (x d) (y d)
  in Lattice {
    latticeBottom = EmbPayload [] $ \_ -> latticeBottom lat,
    latticeJoin = embJoin,
    iota = iotaVal,
    lleq = \x y -> fnEquality (embJoin x y) y,
    flowDirection = flowDirection lat
  }

naiveLift :: (label -> payload -> payload) -> (label -> ( d -> payload) -> (d -> payload))
naiveLift f lab lhat = (f lab) . lhat

liftToFn
  :: Int
  -> Lattice (payload) --Our embellished lattice
  -> (Map.Map LabelNode payload -> LabelNode -> payload -> payload) --Original transfer function
  -> ((LabelNode, LabelNode) -> (payload, payload) -> payload) --special 2-value return function
  -> Map.Map LabelNode (EmbPayload LabelNode payload)
  -> LabelNode
  -> (EmbPayload LabelNode payload)
  -> (EmbPayload LabelNode payload)

liftToFn depth lat@Lattice{..} f  _fret resultMap (Call label) (EmbPayload domain lhat) =
  EmbPayload domain $ \d -> case d of
    [] -> latticeBottom
    ( lc:dRest) -> let
          possibleEnds = [ldom | ldom <- domain, (take depth (lc:ldom)) == (lc:dRest) ]
        in joinAll lat [lhat dPoss | dPoss <- possibleEnds]
liftToFn _ _ f fret resultMap rnode@(Return _ label) (EmbPayload domain lhat') =
  let
    (EmbPayload _ lhat) = (resultMap Map.! (Call label) )
  in EmbPayload domain $ \d -> --We assume they have the same domain 
    fret (Call label, rnode)  (lhat d, lhat' ((Call label):d) )
liftToFn _ _ _ _ _ _ lhat = lhat

--TODO need reverse graph?
callGraph :: LabeledExpr -> Map.Map Label [Label]
callGraph (A _ (Let defs _)) =
  let
    fnNames = map (\(GenericDef (Pattern.Var n) _ _) -> nameToCanonVar n) defs
    fnBodies = map (\(GenericDef _ body _) -> functionBody body ) defs
    fnLabels = map functionLabel defs
    labelDict = Map.fromList $ zip fnNames fnLabels

    oneLevelCalls () expr subCalls = (concat subCalls) ++ case expr of
      (A _ (App (A _ (Var fnName)) _)) ->
        if (Map.member fnName labelDict)
           then [labelDict Map.! fnName]
           else []
      _ -> []

    allCalls = foldE
      (\_ () -> repeat ())
      ()
      (\(GenericDef _ e v) -> [e])
      oneLevelCalls

    callMap = Map.fromList $ zip fnLabels $ map (\body -> allCalls body) fnBodies
  in callMap

contextDomain :: Int -> Map.Map Label [Label] -> [[Label]]
contextDomain n callMap = let
    allLabels = Map.keys callMap
  in helper n callMap ([[]] ++ map (\x -> [x]) allLabels)
  where 
    helper 0 _ _ = [[]]
    helper 1 _ accum = accum
    helper n callMap accum = let
        oneLevelPaths = [ (l2:l1:callStr) |
                         (l1:callStr) <- accum,
                         l2 <- (callMap Map.! l1)]
        newAccum = List.nub $ accum ++ oneLevelPaths
      in helper (n-1) callMap newAccum
