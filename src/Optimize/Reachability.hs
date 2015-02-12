module Reachability where

import Optimize.MonotoneFramework

newtype IsReachable = IsReachable {fromReachable :: Bool}
  deriving (Eq, Ord)

{-|
A simple reachability test.
When we use this lattice, our worklist algorithm basically
becomes a depth-first search on a graph,
returning a boolean for each label for whether it is reachable
from our initial extremal values
|-}
instance Lattice IsReachable where
  latticeBottom = IsReachable False
  latticeJoin a b = IsReachable (fromReachable a || fromReachable b )
  iota = IsReachable True
  lleq a b = (latticeJoin a b) == b 
  
