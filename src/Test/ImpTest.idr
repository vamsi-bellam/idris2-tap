module Test.ImpTest

import Examples.Imp

import Test.Utils

sampleImpProgram : String 
sampleImpProgram = 
  """
    n := 10;
    sum := 0;
    while n <= 0 do 
      sum := sum + n;
      if n = 5 then 
        skip
      else
        n := n - 1
      done
    done
  """

i1 : Test
i1 = 
  MkTest 
    "Imp Language - Example" 
    (assertEq 
      (parseCommand sampleImpProgram) 
      (Right 
        (Seq (Assign ("n", VInt 10)
        , Seq (Assign ("sum", VInt 0)
              , While 
                (LTE (Loc "n", VInt 0)
                  , Seq (Assign ("sum", Plus (Loc "sum", Loc "n"))
                        , ITE (Eq(Loc "n", VInt 5)
                            , Skip
                            , Assign ("n", Minus (Loc "n", VInt 1))))))))))

tests : List Test 
tests = 
  [
    i1
  ]

export 
impTests : TestSuite
impTests = MkTestSuite "IMP Tests" tests