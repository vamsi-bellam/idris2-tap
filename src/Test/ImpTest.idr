module Test.ImpTest

import Examples.Imp

import Test.Utils


i1 : Test
i1 = 
  MkTest 
    "Imp Language - Arith Expression" 
    (assertEq 
      (parseCommand "x := 1 + 2 * 3 - 4 * 5 + 6") 
      (Right (Assign 
                ("x", 
                Plus 
                  (VInt 1, 
                  Minus (
                    Mult (VInt 2, VInt 3), 
                    Plus (
                      Mult (VInt 4, VInt 5), 
                      VInt 6)))))))

i2 : Test
i2 = 
  MkTest 
    "Imp Language - Bool Expression" 
    (assertEq 
      (parseCommand "while (!true && !false || (!(true || false))) do skip done") 
      (Right (While 
                (Or (
                    And (Not (VTrue), Not (VFalse)), 
                    Not (Or (VTrue, VFalse))
                    ), 
                  Skip))))

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

i3 : Test
i3 = 
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
  , i2
  , i3
  ]

export 
impTests : TestSuite
impTests = MkTestSuite "IMP Tests" tests