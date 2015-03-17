module ImperativeTest where

import State.Escapable (..)
import Text (..)
import Graphics.Element (..)

controlDepTest : Int -> EState ph Int
controlDepTest x = 
  newRef 0 `andThen` \ref ->
  let 
    y = x - 1
    z = x * 2
  in 
    (if z > 0
     then writeRef ref 100
     else writeRef ref 200
     ) `andThen` \_ ->
   deRef ref

{-
basicStateTest : Int -> Maybe a -> EState ph Int
basicStateTest x y =
  (if (x <= 0)
    then newRef 1 
    else newRef x) `andThen` \ref ->
  deRef ref `andThen` \newX ->
  writeRef ref (2*newX) `andThen` \_ ->
  (case y of
    Just _ -> writeRef ref (3*newX)
    Nothing -> writeRef ref (4*newX))
      `andThen` \_ ->
  deRef ref

stateFn : Int -> StateRef ph Int -> EState ph {}
stateFn x ref =
  deRef ref `andThen` \oldVal -> 
  writeRef ref 0 `andThen` \_ ->
  basicStateTest x (Just 20) `andThen` \fnRet ->
  writeRef ref (fnRet + oldVal) `andThen` \_ ->
  liftToState {}

stateFnCaller : Int -> EState ph Int
stateFnCaller x = 
  newRef 100 `andThen` \ref ->
  stateFn x ref `andThen` \_ ->
  deRef ref 
-}
main = 
  flow down
    [ 
      asText <| runState <| controlDepTest -100
      -- asText <| runState <| basicStateTest 10 (Just 20)
      --, asText <| runState <| stateFnCaller 20
    ]
