module Main

import Examples.SExpressions
import Examples.Json
import Examples.Imp
import Token


optionsNote : String 
optionsNote =
  """ 
  Select Parsers to use 
  1. Sexp 
  2. Json 
  3. Imp Language

  Type :q to Quit \n
  """

runParser : Show a => (String -> Either String a) -> IO ()
runParser parser = do 
  putStrLn "\nPlease enter the input string \n"
  input <- getLine 
  case (parser input) of 
    Left error => putStrLn "Error : \{error} \n"
    Right ans => do
      putStrLn ("\nParsed Result => " ++ show ans)
      -- case rest of 
      --   [] => putStrLn "\nEntire input is parsed!! \n"
      --   _ => putStrLn ("\nRemaining String => " ++ pack rest ++ "\n")



handleOption : String -> IO ()
handleOption "1" = runParser parseSexp
handleOption "2" = runParser parseJSON
handleOption "3" = runParser parseCommand
handleOption "4" = runParser parseBool
handleOption "5" = runParser parseArith
handleOption str = putStrLn "Invalid Option. Please choose again!\n"

main : IO ()
main = do
  putStrLn optionsNote
  option <- getLine
  case option of
        ":q" => putStrLn "Good Bye!"
        _    => do
          handleOption option
          main


