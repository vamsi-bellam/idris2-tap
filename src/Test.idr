module Test 

import Examples.SExpressions
import Examples.Json

data TestResult = Pass | Failed String

record Test where 
  constructor MkTest
  name : String 
  result : TestResult

Interpolation Int where
  interpolate x = cast x

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
      putStrLn "\{name} : Failed - \{msg} \n"
      runTestsHelper xs (x, y+1)


assertEq : Eq a => (given : a) -> (expected : a) -> TestResult
assertEq g e = if g == e then Pass else Failed "Expected not equal to given!"

-- SExpression tests 

sexample1 : Test
sexample1 = 
  MkTest 
    "String with single bracket" 
    (assertEq 
      (parseSexp "(Programming)") 
      (Right (Sequence [Sym "Programming"], [])))

sexample2 : Test
sexample2 = 
  MkTest 
    "String without braces" 
    (assertEq (parseSexp "Programming") (Right (Sym "Programming", [])))

sexample3 : Test
sexample3 = 
  MkTest 
    "More braces with single string" 
    (assertEq 
      (parseSexp "(((Programming)))") 
      (Right (Sequence [Sequence [Sequence [Sym "Programming"]]], [])))

sexample4 : Test
sexample4 = 
  MkTest 
    "More braces with more strings" 
    (assertEq 
      (parseSexp "(Functional((Programming)))") 
      (Right 
        (Sequence [Sym "Functional", Sequence [Sequence [Sym "Programming"]]], 
        [])))

sexample5 : Test
sexample5 = 
  MkTest 
    "Empty braces" 
    (assertEq 
      (parseSexp "(())") 
      (Right (Sequence [Sequence []], [])))

sexample6 : Test
sexample6 = 
  MkTest
    "Braces in wrong order"
    (assertEq 
      (parseSexp ")Prog(") 
      (Left "No Progress possible, unexpected token - ')'"))

sexample7 : Test
sexample7 = 
  MkTest
    "Incomplete sexpression string"
    (assertEq (parseSexp "(((Prog)") (Left "Unexpected end of stream"))


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


-- JSON tests 
jsonExample1 : Test
jsonExample1 = 
  MkTest 
    "Json - string" 
    (assertEq 
      (parseJSON "\"Programming\"") 
      (Right (JString "Programming", [])))

jsonExample2 : Test
jsonExample2 = 
  MkTest 
    "Json - True" 
    (assertEq 
      (parseJSON "true") 
      (Right (JBool True, [])))

jsonExample3 : Test
jsonExample3 = 
  MkTest 
    "Json - False" 
    (assertEq 
      (parseJSON "false") 
      (Right (JBool False, [])))

jsonExample4 : Test
jsonExample4 = 
  MkTest 
    "Json - null" 
    (assertEq 
      (parseJSON "null") 
      (Right (JNull, [])))

jsonExample5 : Test
jsonExample5 = 
  MkTest 
    "Json - Object" 
    (assertEq 
      (parseJSON "{\"name\":\"vamsi\",\"age\":25,\"interests\":[\"cricket\"]}") 
      (Right 
        (JObject 
          [ ("name", JString "vamsi")
          , ("age", JDecimal 25.0)
          , ("interests", JArray [JString "cricket"])
          ], 
        [])))

jsonExample6 : Test
jsonExample6 = 
  MkTest 
    "Json - Array" 
    (assertEq 
      (parseJSON "[\"Fundamentals of PL\",35.789,null,false]") 
      (Right 
        (JArray 
          [JString "Fundamentals of PL", JDecimal 35.789, JNull, JBool False], 
        [])))

jsonExample7 : Test
jsonExample7 = 
  MkTest 
    "Json string with special chars" 
    (assertEq 
      (parseJSON "\"!@#$%^&*()Qwertyuiop{}[\r\t]||Asdfghjkl:;'Zxcvbnm<,>.?\"") 
      (Right 
        (JString "!@#$%^&*()Qwertyuiop{}[\r\t]||Asdfghjkl:;'Zxcvbnm<,>.?", [])))

jsonExample8 : Test
jsonExample8 = 
  MkTest 
    "Invalid Json" 
    (assertEq 
      (parseJSON "[false)") 
      ((Left "No Progress possible, unexpected token - ')'")))

jsonExample9 : Test
jsonExample9 = 
  MkTest 
    "Incomplete Json" 
    (assertEq 
      (parseJSON "[false,34,") 
      (Left "Unexpected end of stream"))

jsonTests : List Test 
jsonTests = 
  [
    jsonExample1
  , jsonExample2
  , jsonExample3
  , jsonExample4
  , jsonExample5
  , jsonExample6
  , jsonExample7
  , jsonExample8
  , jsonExample9
  ]

testSuiteName : String -> String 
testSuiteName name = "----- \{name} -----\n"

main : IO ()
main = 
  do 
    putStrLn $ testSuiteName "SExpression Tests"
    runTests sexpTests
    putStrLn $ testSuiteName "JSON Tests"
    runTests jsonTests