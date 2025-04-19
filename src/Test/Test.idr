module Test.Test

import Examples.Json
import Examples.Imp

import Test.Utils
import Test.SexpTest
import Test.JsonTest
import Test.ImpTest


main : IO ()
main = runTestSuite [sexpTests, jsonTests, impTests]