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
Parser tagType a  = 
  List (Token tagType) -> Either String (a, List (Token tagType))

bot : Parser tagType a
bot _ = Left "Impossible"

eps : a -> Parser tagType a
eps v rest = Right (v, rest)

token : {a : Type} 
     -> {tagType : Type -> Type} 
     -> {auto _ : Tag tagType} 
     -> (c : tagType a)
     -> Parser tagType a
token c [] = Left "Expected \{Token.show c}, reached end of the stream"
token c (Tok tg v :: xs) = 
  case (compare c tg) of 
        Eql => Right(v, xs)
        _ => Left "Expected \{Token.show c}, got \{Token.show tg}"

seq : Parser tagType a -> Parser tagType b -> Parser tagType (a, b)
seq p1 p2 cs = 
  do 
    (a, rest) <- p1 cs 
    (b, rest) <- p2 rest
    Right ((a, b), rest)

alt : {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> LangType (TokenType tagType) 
   -> Parser tagType a 
   -> LangType (TokenType tagType) 
   -> Parser tagType a 
   -> Parser tagType a
alt l1 p1 l2 p2 cs = 
  case head' cs of 
    Nothing =>  if l1.null then p1 cs 
                else if l2.null then p2 cs 
                else Left "Unexpected end of stream"
    Just (Tok tg v) => 
      if contains (TokType tg) l1.first then 
        p1 cs
      else if contains (TokType tg) l2.first then
        p2 cs
      else if l1.null then
        p1 cs 
      else if l2.null then
        p2 cs 
      else 
        Left "No Progress possible, unexpected token - \{Token.show tg}"  

map : (a -> b) -> Parser tagType a -> Parser tagType b
map f p cs = 
  do 
    (a, rest) <- p cs
    Right (f a , rest)

data ParseEnv : (tagType : Type -> Type) -> Vect n Type -> Type where
  Empty  : ParseEnv tagType []
  (::) : Parser tagType a -> ParseEnv tagType as -> ParseEnv tagType (a :: as)

lookup : Var a ct -> ParseEnv tagType ct -> Parser tagType a 
lookup Z (x :: _ ) = x
lookup (S k) (_ :: xs) = lookup k xs

export 
parse : {a : Type} 
     -> {ct : Vect n Type} 
     -> {tagType : Type -> Type} 
     -> {auto _ : Tag tagType} 
     -> Grammar ct a tagType 
     -> ParseEnv tagType ct 
     -> Parser tagType a
parse (MkGrammar _ (Eps g)) penv = eps g

parse (MkGrammar _ (Seq g1 g2)) penv =
  let p1 = parse g1 penv
      p2 = parse g2 penv
  in
  seq p1 p2

parse (MkGrammar _ (Tok c)) penv = token c

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
      fix : (Parser tagType a -> Parser tagType a) -> Parser tagType a
      fix f input = f (fix f) input

parse (MkGrammar _ (Var var)) penv = lookup var penv


export
generateParser : {a: Type} 
              -> {tagType : Type -> Type} 
              -> {auto _ : Tag tagType} 
              -> Grammar Nil a tagType 
              -> Either String (Parser tagType a)
generateParser gram = 
  do 
    typedGrammar <- typeCheck gram 
    Right (parse typedGrammar Empty)