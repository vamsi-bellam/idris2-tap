module Test.Utils 

public export
data TestResult = Pass | Failed String

public export
record Test where 
  constructor MkTest
  name : String 
  result : TestResult

public export
record TestSuite where 
  constructor MkTestSuite
  name : String 
  test : List Test

Interpolation Int where
  interpolate x = cast x

public export
runTests : List Test -> IO ()
runTests tests = runTestsHelper tests (0, 0) where 
  runTestsHelper : List Test -> (Int, Int) -> IO ()
  runTestsHelper [] (x, y) = 
    if x == 0 then putStrLn "No Tests!" 
    else 
      putStrLn "\{x} / \{y} tests passed \n"
  runTestsHelper ((MkTest name Pass) :: xs) (x, y) = 
    do
      putStrLn "\{name} : Passed \n"
      runTestsHelper xs (x+1, y+1)
  runTestsHelper ((MkTest name (Failed msg)) :: xs) (x, y) =
    do
      putStrLn "\{name} : Failed \n\{msg} \n"
      runTestsHelper xs (x, y+1)


testSuiteName : String -> String 
testSuiteName name = "----- \{name} -----\n"

public export
runTestSuite : List TestSuite -> IO ()
runTestSuite [] = putStrLn "---- Tests Completed ----"
runTestSuite (MkTestSuite name tests :: xs) = do
  putStrLn $ testSuiteName name
  runTests tests 
  runTestSuite xs
    


public export
assertEq : {auto _ : Show a} 
        -> {auto _ : Eq a} 
        -> (given : a) 
        -> (expected : a)
        -> TestResult
assertEq g e = 
  if g == e then Pass 
  else Failed ("Expected - " ++ show e ++ "\n" ++ "Given - " ++ show g)