{-# LANGUAGE RecordWildCards, ScopedTypeVariables, FlexibleContexts #-}
module Optimize.EmbellishedMonotone where

import Optimize.MonotoneFramework
import Optimize.Types
import Optimize.ControlFlow

import qualified Data.Map as Map

newtype EmbPayload a b = EmbPayload (a -> b)

liftJoin
  :: Lattice payload
  -> (EmbPayload d payload)
  -> (EmbPayload d payload)
  -> (EmbPayload d payload)
liftJoin lat = \(EmbPayload x) (EmbPayload y) ->
  EmbPayload $ \ d -> (latticeJoin lat) (x d) (y d)

liftToEmbellished
  :: (Eq (EmbPayload d payload))
  => Lattice payload
  -> Lattice (EmbPayload d payload)
liftToEmbellished lat =
  Lattice {
    latticeBottom = EmbPayload $ \_ -> latticeBottom lat,
    latticeJoin = \ (EmbPayload x) (EmbPayload y)
                  -> EmbPayload $ \d -> (latticeJoin lat) (x d) (y d),
    iota = EmbPayload $ \_ -> iota lat,
    lleq = \x y -> (liftJoin lat x y) == y
  }

naiveLift :: (label -> payload -> payload) -> (label -> ( d -> payload) -> (d -> payload))
naiveLift f lab lhat = (f lab) . lhat

liftToFn
  :: Lattice (payload) --Our embellished lattice
  -> (Map.Map LabelNode payload -> LabelNode -> payload -> payload) --Original transfer function
  -> ((LabelNode, LabelNode) -> (payload, payload) -> payload) --special 2-value return function
  -> Map.Map LabelNode (EmbPayload [LabelNode] payload)
  -> LabelNode
  -> (EmbPayload [LabelNode] payload)
  -> (EmbPayload [LabelNode] payload)

liftToFn Lattice{..} f  _fret resultMap (Call label) (EmbPayload lhat) =
  EmbPayload $ \d -> case d of
    [] -> latticeBottom
    ( lc@(Call lcn) : dRest) -> if (lcn == label)
                   then f (Map.map (\(EmbPayload lh) -> lh d ) resultMap) lc (lhat d)
                   else error "Invalid call-string"
liftToFn _ f fret resultMap rnode@(Return _ label) (EmbPayload lhat') =
  EmbPayload $ \d -> 
    let
      (EmbPayload lhat) = (resultMap Map.! (Call label) )
    in fret (Call label, rnode)  (lhat d, lhat' ((Call label):d) )
liftToFn _ _ _ _ _ lhat = lhat
