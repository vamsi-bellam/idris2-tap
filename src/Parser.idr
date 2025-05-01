module Parser

import Data.List
import Data.SortedSet
import Data.Vect


import Language
import Grammar
import Var
import Token


public export
Parser : Type -> (Type -> Type) -> Type 
Parser a tagType  = 
  List (Token tagType) -> Either String (a, List (Token tagType))

bot : Parser a tagType
bot _ = Left "Impossible"

eps : a -> Parser a tagType
eps v rest = Right (v, rest)

token : {a : Type} 
     -> {tagType : Type -> Type} 
     -> {auto _ : Tag tagType} 
     -> (tag : tagType a)
     -> Parser a tagType
token tag [] = Left "Expected \{Token.show tag}, reached end of the stream"
token tag (Tok tag' value :: rest) = 
  case (compare tag tag') of 
        Eql => Right(value, rest)
        _ => Left "Expected \{Token.show tag}, got \{Token.show tag'}"

seq : Parser a tagType -> Parser b tagType -> Parser (a, b) tagType
seq p1 p2 cs = 
  do 
    (a, rest) <- p1 cs 
    (b, rest) <- p2 rest
    Right ((a, b), rest)

alt : {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> LangType (TokenType tagType) 
   -> Parser a tagType 
   -> LangType (TokenType tagType) 
   -> Parser a tagType 
   -> Parser a tagType
alt l1 p1 l2 p2 cs = 
  case head' cs of 
    Nothing =>  if l1.null then p1 cs 
                else if l2.null then p2 cs 
                else Left "Unexpected end of stream"
    Just (Tok tag v) => 
      if contains (TokType tag) l1.first then 
        p1 cs
      else if contains (TokType tag) l2.first then
        p2 cs
      else if l1.null then
        p1 cs 
      else if l2.null then
        p2 cs 
      else 
        Left "No Progress possible, unexpected token - \{Token.show tag}"  

map : (a -> b) -> Parser a tagType -> Parser b tagType
map f p cs = 
  do 
    (a, rest) <- p cs
    Right (f a , rest)

data ParseEnv : (tagType : Type -> Type) -> Vect n Type -> Type where
  Empty  : ParseEnv tagType []
  (::) : Parser a tagType -> ParseEnv tagType as -> ParseEnv tagType (a :: as)

lookup : Var a ct -> ParseEnv tagType ct -> Parser a tagType 
lookup Z (x :: _ ) = x
lookup (S k) (_ :: xs) = lookup k xs
 
parse : {a : Type} 
     -> {ct : Vect n Type} 
     -> {tagType : Type -> Type} 
     -> {auto _ : Tag tagType} 
     -> Grammar ct a tagType 
     -> ParseEnv tagType ct 
     -> Parser a tagType
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

parse (MkGrammar _ (Map g f)) penv = map f $ parse g penv 

parse (MkGrammar _ (Fix g)) penv = 
  fix (\p => parse g (p :: penv))
    where
      fix : (Parser a tagType -> Parser a tagType) -> Parser a tagType
      fix f input = f (fix f) input

parse (MkGrammar _ (Var var)) penv = lookup var penv


export
generateParser : {a: Type} 
              -> {tagType : Type -> Type} 
              -> {auto _ : Tag tagType} 
              -> Grammar Nil a tagType 
              -> Parser a tagType
generateParser typedGrammar = parse typedGrammar Empty