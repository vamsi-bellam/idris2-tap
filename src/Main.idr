module Main

import Examples.SExpressions
import Examples.Json


optionsNote : String 
optionsNote =
  """ 
  Select Parsers to use 
  1. Sexp 
  2. Json 

  Type :q to Quit \n
  """

runParser : Show a => (String -> Either String (a, List Char)) -> IO ()
runParser parser = do 
  putStrLn "\nPlease enter the input string \n"
  input <- getLine 
  case (parser input) of 
    Left error => putStrLn "Error : \{error} \n"
    Right (ans, rest) => 
      putStrLn ("\nParsed Result => " ++ show ans ++ "\nRemaining String => " ++ pack rest ++ "\n")



handleOption : String -> IO ()
handleOption "1" = runParser parseSexp
handleOption "2" = runParser parseJSON
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


