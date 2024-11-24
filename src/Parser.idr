module Parser
import Data.List
import Data.SortedSet
import Data.Vect
import Language
import Grammar

public export
Parser : Type -> Type 
Parser a  = List Char -> Either String (a , List Char)

public export
bot : Parser a
bot _ = Left "Impossible"

public export
eps : Either String (a , List Char) -> Parser a
eps v _ = v

public export
chr : Char -> Parser Char
chr c [] = Left "Expected \{show c}, reached end of the stream"
chr c (x :: xs) = 
    if x == c then Right (x, xs) else Left "Expected \{show c}, got \{show x}"

public export 
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

public export
map : (a -> b) -> Parser a -> Parser b
map f p cs = 
  do 
    (a, rest) <- p cs
    Right (f a , rest)

public export
data ParseEnv : Vect n Type -> Type where
  Nil  : ParseEnv []
  (::) : Parser a -> ParseEnv as -> ParseEnv (a :: as)

public export
lookup : (i : Fin n) -> ParseEnv ts -> Parser (index i ts)
lookup FZ (p :: _) = p
lookup (FS k) (_ :: ps) = lookup k ps


-- Takes type checked grammar and produce the parser
public export 
parse : {n : Nat} -> {ct : Vect n Type} -> Grammar n a -> ParseEnv ct -> Parser a
parse (MkGrammar _ (Eps g)) penv = eps (Right (g, []))
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
parse (MkGrammar _ (Fix x)) penv = ?ll_7
parse (MkGrammar _ (Var x)) penv = lookup x penv


public export
applyParse : Either String (Parser Char) ->  
            List Char -> Either String (Char , List Char)
applyParse p cs = 
  do 
    par <- p
    par cs