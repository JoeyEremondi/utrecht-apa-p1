{-# LANGUAGE RecordWildCards, ScopedTypeVariables, FlexibleContexts #-}
module Optimize.EmbellishedMonotone where

import Optimize.MonotoneFramework
import Optimize.Types
import Optimize.ControlFlow

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
  :: Lattice (payload) --Our embellished lattice
  -> (Map.Map LabelNode payload -> LabelNode -> payload -> payload) --Original transfer function
  -> ((LabelNode, LabelNode) -> (payload, payload) -> payload) --special 2-value return function
  -> Map.Map LabelNode (EmbPayload LabelNode payload)
  -> LabelNode
  -> (EmbPayload LabelNode payload)
  -> (EmbPayload LabelNode payload)

liftToFn Lattice{..} f  _fret resultMap (Call label) (EmbPayload domain lhat) =
  EmbPayload domain $ \d -> case d of
    [] -> latticeBottom
    ( lc@(Call lcn) : dRest) -> if (lcn == label)
                   then f (Map.map (\(EmbPayload domain lh) -> lh d ) resultMap) lc (lhat d)
                   else error "Invalid call-string"
liftToFn _ f fret resultMap rnode@(Return _ label) (EmbPayload domain lhat') =
  let
    (EmbPayload _ lhat) = (resultMap Map.! (Call label) )
  in EmbPayload domain $ \d -> --We assume they have the same domain 
    fret (Call label, rnode)  (lhat d, lhat' ((Call label):d) )
liftToFn _ _ _ _ _ lhat = lhat
