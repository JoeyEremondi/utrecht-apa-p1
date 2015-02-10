module SyntaxTest where

import Text

fibTest : Int -> Int
fibTest n = case n of
  0 -> 1
  1 -> 1
  _ -> (fibTest n-2) + (fibTest n-1)

tailCallFib n = 
    if n < 2
    then 1
    else let
      helper i n1 n2 = 
        if i >= n
        then n2
        else helper (i+1) n2 (n1 + n2)
    in helper 2 1 1

opsOrder = 3 + 4 - 5 - 6 + 7 - 8


listTest : List Int -> List Int
listTest l = case l of
  [1,2,3] -> [4,5,6]
  (1::3::l)  -> (2 :: 4::l)
  l -> l ++ [4,5,6] ++ (7::8::9::[])
      


main = Text.plainText "Hello"