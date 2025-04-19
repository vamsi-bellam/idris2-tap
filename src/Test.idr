module Test 

import Examples.SExpressions
import Examples.Json
import Examples.Imp

import Token

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
      putStrLn "\{name} : Failed \n\{msg} \n"
      runTestsHelper xs (x, y+1)


assertEq : Show a => Eq a => (given : a) -> (expected : a) -> TestResult
assertEq g e = 
  if g == e then Pass 
  else Failed ("Expected - " ++ show e ++ "\n" ++ "Given - " ++ show g)

-- SExpression tests 

s1 : Test
s1 = 
  MkTest 
    "Just String" 
    (assertEq 
      (parseSexp "Programming") 
      (Right (Sym "Programming")))

s2 : Test
s2 = 
  MkTest 
    "Empty braces" 
    (assertEq 
      (parseSexp "(())") 
      (Right (Sequence [Sequence []])))

s3 : Test
s3 = 
  MkTest 
    "String with single bracket" 
    (assertEq 
      (parseSexp "(Programming)") 
      (Right (Sequence [Sym "Programming"])))

s4 : Test
s4 = 
  MkTest 
    "More braces with single string" 
    (assertEq 
      (parseSexp "(((Programming)))") 
      (Right (Sequence [Sequence [Sequence [Sym "Programming"]]])))

s5 : Test
s5 = 
  MkTest 
    "More braces with more strings" 
    (assertEq 
      (parseSexp "(Functional((Programming)))") 
      (Right 
        (Sequence [Sym "Functional", Sequence [Sequence [Sym "Programming"]]])))

s6 : Test
s6 = 
  MkTest
    "Braces in wrong order"
    (assertEq 
      (parseSexp ")Prog(") 
      (Left "No Progress possible, unexpected token - RParen"))

s7 : Test
s7 = 
  MkTest
    "Incomplete sexpression string"
    (assertEq (parseSexp "(((Prog)") (Left "Expected RParen, reached end of the stream"))

s8 : Test
s8 = 
  MkTest
    "Correct braces, but invalid string"
    (assertEq (parseSexp "((*Programming))") 
    (Left "No Progress possible, unexpected token - '*'"))

s9 : Test
s9 = 
  MkTest
    "Valid Sexp and have remaining string"
    (assertEq (parseSexp "(Programming)12345") 
    (Left "No Progress possible, unexpected token - '1'" ))

s10 : Test
s10 = 
  MkTest
    "Long sexpression"
    (assertEq 
    (parseSexp "((Abd)(Bfbew)(Bfebwrew)((Jkedqbd)((((Ojdewbrbd)))))((Idbejqwrbwbd)(Pjqeqbd)(Ljdqwbebd)(Mqwjbebd)(Sdjebrbd)((Ygqveqdagdvewwhevq))))") 
    (Right 
      (Sequence [Sequence [Sym "Abd"], Sequence [Sym "Bfbew"], 
       Sequence [Sym "Bfebwrew"], Sequence [Sequence [Sym "Jkedqbd"], 
       Sequence [Sequence [Sequence [Sequence [Sym "Ojdewbrbd"]]]]], 
       Sequence [Sequence [Sym "Idbejqwrbwbd"], Sequence [Sym "Pjqeqbd"], 
       Sequence [Sym "Ljdqwbebd"], Sequence [Sym "Mqwjbebd"], 
       Sequence [Sym "Sdjebrbd"], 
       Sequence [Sequence [Sym "Ygqveqdagdvewwhevq"]]]])))

s11 : Test
s11 = 
  MkTest 
    "More braces with more strings and spaces" 
    (assertEq 
      (parseSexp "   ( Functional   (    (Programming))     )   ") 
      (Right 
        (Sequence [Sym "Functional", Sequence [Sequence [Sym "Programming"]]])))

sexpTests : List Test 
sexpTests = 
  [
    s1
  , s2
  , s3
  , s4
  , s5
  , s6
  , s7
  , s8
  , s9
  , s10
  , s11
  ]


-- JSON tests 
j1 : Test
j1 = 
  MkTest 
    "Json - string" 
    (assertEq 
      (parseJSON "\"Programming\"") 
      (Right (JString "Programming")))

j2 : Test
j2 = 
  MkTest 
    "Json - True" 
    (assertEq 
      (parseJSON "true") 
      (Right (JBool True)))

j3 : Test
j3 = 
  MkTest 
    "Json - False" 
    (assertEq 
      (parseJSON "false") 
      (Right (JBool False)))

j4 : Test
j4 = 
  MkTest 
    "Json - null" 
    (assertEq 
      (parseJSON "null") 
      (Right (JNull)))

j5 : Test
j5 = 
  MkTest 
    "Json - Object" 
    (assertEq 
      (parseJSON "{\"name\":\"vamsi\",\"gpa\":3.85,\"interests\":[\"cricket\"]}") 
      (Right 
        (JObject 
          [ ("name", JString "vamsi")
          , ("gpa", JDecimal 3.85)
          , ("interests", JArray [JString "cricket"])
          ])))

j6 : Test
j6 = 
  MkTest 
    "Json - Array" 
    (assertEq 
      (parseJSON "[\"Fundamentals of PL\",35.789,null,false]") 
      (Right 
        (JArray 
          [JString "Fundamentals of PL", JDecimal 35.789, JNull, JBool False])))

j7 : Test
j7 = 
  MkTest 
    "Json string with special chars" 
    (assertEq 
      (parseJSON "\"!@#$%^&*()Qwertyuiop{}[\r\t]||Asdfghjkl:;'Zxcvbnm<,>.?\"") 
      (Right 
        (JString "!@#$%^&*()Qwertyuiop{}[\r\t]||Asdfghjkl:;'Zxcvbnm<,>.?")))

j8 : Test
j8 = 
  MkTest 
    "Invalid Json" 
    (assertEq 
      (parseJSON "[false)") 
      ((Left "No Progress possible, unexpected token - ')'")))

j9 : Test
j9 = 
  MkTest 
    "Incomplete Json" 
    (assertEq 
      (parseJSON "[false,34,") 
      (Left "Expected TRBracket, reached end of the stream"))

j10 : Test
j10 = 
  MkTest 
    "Json - With Spaces" 
    (assertEq 
      (parseJSON "{ \"name\" : \"vamsi\", \"gpa\" : 3.85, \"interests\" : [\"cricket\"] }") 
      (Right 
        (JObject 
          [ ("name", JString "vamsi")
          , ("gpa", JDecimal 3.85)
          , ("interests", JArray [JString "cricket"])
          ])))

j11 : Test
j11 = 
  MkTest 
    "Json - With New Lines" 
    (assertEq 
      (parseJSON exampleJSON) 
      (Right 
        (JObject 
          [ ("name", JString "vamsi")
          , ("gpa", JDecimal 3.85)
          , ("interests", JArray [JString "cricket"])
          ])))
  where 
    exampleJSON : String 
    exampleJSON = 
      """
        { 
          \"name\" : \"vamsi\", 
          \"gpa\" : 3.85, 
          \"interests\" : [\"cricket\"] 
        }
      """

jsonTests : List Test 
jsonTests = 
  [
    j1
  , j2
  , j3
  , j4
  , j5
  , j6
  , j7
  , j8
  , j9
  , j10
  , j11
  ]


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

impTests : List Test 
impTests = 
  [
    i1
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
    putStrLn $ testSuiteName "IMP Language Tests"
    runTests impTests