{-# LANGUAGE RecordWildCards #-}
module Optimize.EmbellishedMonotone where

import Optimize.MonotoneFramework
import Optimize.Types


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
  :: Eq label
  => Lattice ([label] -> payload)
  -> (label -> payload -> payload) --Original transfer function
  -> (label -> payload -> payload ) --Call-site transfer function
  -> (label -> payload -> payload ) --return site transfer function
  -> (FnLabel label)
  -> ([label] -> payload)
  -> ([label] -> payload)
liftToFn _ f fcall fret (Intra l) = (naiveLift f) l
liftToFn Lattice{..} _f fcall fret (FnCall l) =
  \lhat d -> case d of
    [] -> latticeBottom d
    (lc:d') -> if lc == l
               then fcall lc (lhat d')
               else error "Call with invalid top elem"
    
liftToFn _ _f fcall fret (FnReturn l) = error "TODO return emb" --TODO same label call and return?
liftToFn _ _f fcall fret (FnEnter l) = id
liftToFn _ _f fcall fret (FnExit l) = id 
