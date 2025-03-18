module Parser
import Data.List
import Data.SortedSet
import Data.Vect
import Language
import Grammar
import Env


public export
Parser : Type -> Type 
Parser a  = List Char -> Either String (a , List Char)

bot : Parser a
bot _ = Left "Impossible"

eps : a -> Parser a
eps v rest = Right (v, rest)

chr : Char -> Parser Char
chr c [] = Left "Expected \{show c}, reached end of the stream"
chr c (x :: xs) = 
    if x == c then Right (x, xs) else Left "Expected \{show c}, got \{show x}"

seq : Parser a -> Parser b -> Parser (a, b)
seq p1 p2 cs = 
  do 
    (a, rest) <- p1 cs 
    (b, rest) <- p2 rest
    Right ((a, b), rest)

alt : LangType -> Parser a -> LangType -> Parser a -> Parser a
alt l1 p1 l2 p2 cs = 
  case head' cs of 
    Nothing =>  if l1.null then p1 cs 
                else if l2.null then p2 cs 
                else Left "Unexpected end of stream"
    Just hd =>  if contains hd l1.first then 
                  p1 cs
                else if contains hd l2.first then
                  p2 cs
                else if l1.null then
                  p1 cs 
                else if l2.null then
                  p2 cs 
                else 
                  Left "No Progress possible, unexpected token - \{show hd}"  

map : (a -> b) -> Parser a -> Parser b
map f p cs = 
  do 
    (a, rest) <- p cs
    Right (f a , rest)

data ParseEnv : Vect n Type -> Type where
  Empty  : ParseEnv []
  (::) : Parser a -> ParseEnv as -> ParseEnv (a :: as)

lookup : Var a ct -> ParseEnv ct -> Parser a 
lookup Z (x :: _ ) = x
lookup (S k) (_ :: xs) = lookup k xs

export 
parse : {ct : Vect n Type} -> Grammar ct a -> ParseEnv ct -> Parser a
parse (MkGrammar _ (Eps g)) penv = eps g

parse (MkGrammar _ (Seq g1 g2)) penv = 
  let p1 = parse g1 penv
      p2 = parse g2 penv
  in
  seq p1 p2

parse (MkGrammar _ (Chr c)) penv = chr c

parse (MkGrammar _ Bot) penv = bot

parse (MkGrammar _ (Alt g1 g2)) penv = 
  let p1 = parse g1 penv 
      p2 = parse g2 penv
  in
    alt g1.lang p1 g2.lang p2

parse (MkGrammar _ (Map f g)) penv = map f (parse g penv)

parse (MkGrammar _ (Fix g)) penv = 
  fix (\p => parse g (p :: penv))
    where
      fix : (Parser a -> Parser a) -> Parser a
      fix f input = f (fix f) input

parse (MkGrammar _ (Var var)) penv = lookup var penv


export
generateParser : Grammar Nil a -> Either String (Parser a)
generateParser gram = 
  do 
    typedGrammar <- typeCheck gram 
    Right (parse typedGrammar Empty)

export
runParser : Either String (Parser a) ->  
            List Char -> Either String (a , List Char)
runParser parser input = 
  do 
    parser <- parser
    parser input
