module Parser
import Data.List
import Data.SortedSet
import Data.Vect
import Language
import Grammar
import Env
import Token


public export
Parser : (Type -> Type) -> Type -> Type 
Parser tok a  = List (Token tok) -> Either String (a, List (Token tok))

bot : Parser tok a
bot _ = Left "Impossible"

eps : a -> Parser tok a
eps v rest = Right (v, rest)

chr : {a : Type} -> {tok : Type -> Type} -> (c : tok a) -> Tag tok => Parser tok a
chr c [] = Left "Expected \{Token.show c}, reached end of the stream"
chr c (x@(Tok tg v) :: xs) = case (compare c tg) of 
                                    Leq => Left "Expected \{Token.show c}, got \{Token.show tg}"
                                    Eql => Right(v, xs)
                                    Geq => Left "Expected \{Token.show c}, got \{Token.show tg}"

    -- if tg == c then Right (?lx, xs) else Left "Expected \{show c}, got \{show x}"

seq : Parser tok a -> Parser tok b -> Parser tok (a, b)
seq p1 p2 cs = 
  do 
    (a, rest) <- p1 cs 
    (b, rest) <- p2 rest
    Right ((a, b), rest)

alt : {tok : Type -> Type} -> Tag tok => LangType (TokenType tok) -> Parser tok a -> LangType (TokenType tok) -> Parser tok a -> Parser tok a
alt l1 p1 l2 p2 cs = 
  case head' cs of 
    Nothing =>  if l1.null then p1 cs 
                else if l2.null then p2 cs 
                else Left "Unexpected end of stream"
    Just (hd@(Tok tg v)) =>  if contains (TokType tg) l1.first then 
                  p1 cs
                else if contains (TokType tg) l2.first then
                  p2 cs
                else if l1.null then
                  p1 cs 
                else if l2.null then
                  p2 cs 
                else 
                  Left "No Progress possible, unexpected token - \{Token.show tg}"  

map : (a -> b) -> Parser tok a -> Parser tok b
map f p cs = 
  do 
    (a, rest) <- p cs
    Right (f a , rest)

data ParseEnv : (tok : Type -> Type) -> Vect n Type -> Type where
  Empty  : ParseEnv tok []
  (::) : Parser tok a -> ParseEnv tok as -> ParseEnv tok (a :: as)

lookup : Var a ct -> ParseEnv tok ct -> Parser tok a 
lookup Z (x :: _ ) = x
lookup (S k) (_ :: xs) = lookup k xs

export 
parse : {a : Type} -> {tok : Type -> Type} -> Tag tok => {ct : Vect n Type} -> Grammar ct a tok -> ParseEnv tok ct -> Parser tok a
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

parse (MkGrammar _ (Map f g)) penv = let res = parse g penv in map f res

parse (MkGrammar _ (Fix g)) penv = 
  fix (\p => parse g (p :: penv))
    where
      fix : (Parser tok a -> Parser tok a) -> Parser tok a
      fix f input = f (fix f) input

parse (MkGrammar _ (Var var)) penv = lookup var penv


export
generateParser : {a: Type} -> {tok : Type -> Type} -> Tag tok => Grammar Nil a tok -> Either String (Parser tok a)
generateParser gram = 
  do 
    typedGrammar <- typeCheck gram 
    Right (parse typedGrammar Empty)

export
runParser : {a: Type} -> {tok : Type -> Type} -> Tag tok => Either String (Parser tok a) ->  
            List (Token tok) -> Either String (a , List (Token tok))
runParser parser input = 
  do 
    parser <- parser
    parser input
