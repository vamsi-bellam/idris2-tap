module Test.SexpTest

import Examples.SExpressions

import Test.Utils

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
      (Left "No Progress possible, unexpected token - RParen"))

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

tests : List Test 
tests = 
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

export 
sexpTests : TestSuite
sexpTests = MkTestSuite "SExpression Tests" tests