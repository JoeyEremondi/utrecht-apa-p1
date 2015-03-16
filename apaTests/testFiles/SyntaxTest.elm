module SyntaxTest where


ifTest x = 
  let
    vRel = if x > 0 then Just 10 else Nothing
    vNotRel = if x < 10 then Just 100 else Nothing
  in vRel
  
caseTest maybeX = 
  let 
    vNotRel = case maybeX of
             Nothing -> 100
             Just x -> x
    vRel = case maybeX of
      Nothing -> 100
      Just _ -> 200
  in vRel + vRel



multiArgFun x y z = 
  let
     vRel = x+y
     vNotRel1 = x + z
     vNotRel2 = vRel + vNotRel1
  in x*y*z*vRel

--Also tests transitive dependencies
binOpTest x = 
  let
    vRel1 = 2*3 + x
    vNotRel = vRel1 + 10
    vRel2 = vRel1 + 10
  in vRel2 - 100

constThree x = 3

ignoredParamTest = 
  let
      vRel1 = 1
      vRel2 = 2
      vNotRel = vRel1 + vRel2
  in vRel2 + (constThree vRel1)

fnCallTest = 
  let
    vRel = multiArgFun 2 3 4
    vNotRel = multiArgFun 5 6 7
  in vRel + 10

recordTest x y = 
  let
    vRel = {x=x, y=y}
    vNotRel = {x=y, y=x}
  in vRel.x + vRel.y

nestedLetTest x y = 
  let
    vRel1 = 
      let
        vNotRel1 = [0]
        vRel2 = [1,2,3]
        vRel3 = [4,5,6]
      in vRel2 ++ vRel3
    vRel4 = []
    vNotRel2 = vRel4 ++ vRel1
  in vRel4 ++ vRel1 ++ vRel1
      