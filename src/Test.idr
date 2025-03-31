module Test 

import Examples.SExpressions

data TestResult = Pass | Failed String

record Test where 
  constructor MkTest
  name : String 
  result : TestResult

runTests : List Test -> IO ()
runTests [] = putStrLn "Done! \n"
runTests ((MkTest name Pass) :: xs) = 
  do
    putStrLn "\{show name} : Passed \n"
    runTests xs
runTests ((MkTest name (Failed msg)) :: xs) = 
  do
    putStrLn "\{show name} : Failed - \{show msg} \n"
    runTests xs

assertEq : Eq a => (given : a) -> (expected : a) -> TestResult
assertEq g e = if g == e then Pass else Failed "Expected not equal to given!"

-- SExpression tests 

sexample1 : Test
sexample1 = 
  MkTest 
    "String with single bracket" 
    (assertEq 
      (runSexp "(Programming)") 
      (Right (Sequence [Sym "Programming"], [])))

sexample2 : Test
sexample2 = 
  MkTest 
    "Just string without braces" 
    (assertEq (runSexp "Programming") (Right (Sym "Programming", [])))

sexample3 : Test
sexample3 = 
  MkTest 
    "More braces with single string" 
    (assertEq 
      (runSexp "(((Programming)))") 
      (Right (Sequence [Sequence [Sequence [Sym "Programming"]]], [])))

sexample4 : Test
sexample4 = 
  MkTest 
    "More braces with more strings" 
    (assertEq 
      (runSexp "(Functional((Programming)))") 
      (Right 
        (Sequence [Sym "Functional", Sequence [Sequence [Sym "Programming"]]], 
        [])))

sexample5 : Test
sexample5 = 
  MkTest 
    "Just empty braces" 
    (assertEq 
      (runSexp "(())") 
      (Right (Sequence [Sequence []], [])))

sexample6 : Test
sexample6 = 
  MkTest
    "Braces in wrong order"
    (assertEq 
      (runSexp ")Prog(") 
      (Left "No Progress possible, unexpected token - ')'"))

sexample7 : Test
sexample7 = 
  MkTest
    "Incomplete sexpression string"
    (assertEq (runSexp "(((Prog)") (Left "Unexpected end of stream"))


sexpTests : List Test 
sexpTests = 
  [
    sexample1
  , sexample2
  , sexample3
  , sexample4
  , sexample5
  , sexample6
  , sexample7
  ]


main : IO ()
main = runTests sexpTests