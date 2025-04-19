module Test.JsonTest


import Examples.Json

import Test.Utils




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

tests : List Test 
tests = 
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

export 
jsonTests : TestSuite
jsonTests = MkTestSuite "JSON Tests" tests