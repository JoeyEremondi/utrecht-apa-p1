{-# LANGUAGE RecordWildCards, ScopedTypeVariables #-}
module Optimize.EmbellishedMonotone where

import Optimize.MonotoneFramework
import Optimize.Types
import Optimize.ControlFlow

import qualified Data.Map as Map

liftJoin :: Lattice payload -> (d -> payload) -> (d -> payload) -> (d -> payload)
liftJoin lat = \x y d -> (latticeJoin lat) (x d) (y d)

liftToEmbellished :: ((d -> payload) -> (d -> payload) -> Bool) -> Lattice payload -> Lattice (d -> payload)
liftToEmbellished eqInst lat =
  Lattice {
    latticeBottom = \_ -> latticeBottom lat,
    latticeJoin = \ x y d -> (latticeJoin lat) (x d) (y d),
    iota = \_ -> iota lat,
    lleq = \x y -> (liftJoin lat x y) `eqInst` y
  }

naiveLift :: (label -> payload -> payload) -> (label -> ( d -> payload) -> (d -> payload))
naiveLift f lab lhat = (f lab) . lhat

liftToFn
  :: Lattice (payload) --Our embellished lattice
  -> (Map.Map LabelNode payload -> LabelNode -> payload -> payload) --Original transfer function
  -> ((LabelNode, LabelNode) -> (payload, payload) -> payload) --special 2-value return function
  -> Map.Map LabelNode ([LabelNode] -> payload)
  -> LabelNode
  -> ([LabelNode] -> payload)
  -> ([LabelNode] -> payload)

liftToFn Lattice{..} f  _fret resultMap (Call label) lhat =
  \d -> case d of
    [] -> latticeBottom
    ( lc@(Call lcn) : dRest) -> if (lcn == label)
                   then f (Map.map ( $ d ) resultMap) lc (lhat d)
                   else error "Invalid call-string"
liftToFn _ f fret resultMap rnode@(Return _ label) lhat' =
  \d -> 
    let
      lhat = (resultMap Map.! (Call label) )
    in fret (Call label, rnode)  (lhat d, lhat' ((Call label):d) )
liftToFn _ _ _ _ _ lhat = lhat
