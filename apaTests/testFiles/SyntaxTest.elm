module SyntaxTest where


nestedLetTest x y = 
  let
    vRel1 = 
      let
        vRel2 = [1,2,3]
        vRel3 = [4,5,6]
        vNotRel1 = [7,8,9]
        --vNotRel2 = [7,8,9]
        -- vNotRel3 = [7,8,9]
      in vRel2 ++ vRel3
    vRel4 = []
  in vRel4 ++ vRel1 ++ vRel1