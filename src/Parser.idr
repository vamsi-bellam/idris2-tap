module Parser

import Data.List
import Data.SortedSet
import Data.Vect


import Language
import Grammar
import Var
import Token

||| A type alias for a generic parser that consumes a list of typed tokens.
|||
||| `Parser a tagType` represents a parser that:
||| - Consumes a list of `Token tagType` values.
||| - Either fails with an error (`Left String`) or
||| - Succeeds with a value of type `a` and the remaining unconsumed input.
|||
||| @a        The result type of the parser.
||| @tagType  The type of tags that token carries. 
public export
Parser : Type -> (Type -> Type) -> Type 
Parser a tagType  = 
  List (Token tagType) -> Either String (a, List (Token tagType))


||| A parser that always fails with the message `"Impossible"`.
bot : Parser a tagType
bot _ = Left "Impossible"

||| A parser that always succeeds without consuming any input.
|||
||| - Returns the given value `v`.
||| - Leaves the input list unchanged.
|||
||| @v     The value to return without consuming input.
||| @rest  The input stream of tokens (unchanged).
eps : a -> Parser a tagType
eps v rest = Right (v, rest)


||| A parser that matches a single token with the specified tag.
|||
||| It uses the `Tag` interface to compare tags and render informative error messages.
|||
||| @tag The tag of the token to be matched.
||| Requires an instance of `Tag tagType` for comparison and string rendering.
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

||| Sequentially composes two parsers.
|||
||| This parser first applies `p1`, then `p2` on the remaining input.
||| - If both succeed, it returns a pair of their results.
||| - If either fails, the entire composition fails.
|||
||| @p1 The first parser to apply.
||| @p2 The second parser to apply on the remaining input.
||| @cs The input token stream.
seq : Parser a tagType -> Parser b tagType -> Parser (a, b) tagType
seq p1 p2 cs = 
  do 
    (a, rest) <- p1 cs 
    (b, rest) <- p2 rest
    Right ((a, b), rest)

||| Tries two alternative parsers (`p1` and `p2`) based on lookahead and grammar metadata.
|||
||| This parser never backtracks — it is deterministic, driven by `LangType` analysis.
||| @l1 Language metadata for parser `p1`.
||| @p1 First alternative parser.
||| @l2 Language metadata for parser `p2`.
||| @p2 Second alternative parser.
||| @cs Input stream of tokens.
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

||| Transforms the result of a parser using a function.
|||
||| This is the Functor-style `map` combinator:
||| - Applies the parser `p` to the input.
||| - If it succeeds, applies function `f` to the result.
||| - Leaves the remaining input unchanged.
|||
||| @f  The function to apply to the parsed result.
||| @p  The parser whose output should be transformed.
||| @cs The input token stream.
map : (a -> b) -> Parser a tagType -> Parser b tagType
map f p cs = 
  do 
    (a, rest) <- p cs
    Right (f a , rest)


||| Computes the fixed point of a parser transformer.
|||
||| It enables grammars that refer to themselves. 
|||
||| @f A function that takes a parser and returns a new parser (typically recursive).
||| @input The input token stream to parse.
fix : (Parser a tagType -> Parser a tagType) -> Parser a tagType
fix f input = f (fix f) input

data ParseEnv : (tagType : Type -> Type) -> Vect n Type -> Type where
  Empty  : ParseEnv tagType []
  (::) : Parser a tagType -> ParseEnv tagType as -> ParseEnv tagType (a :: as)

lookup : Var a ct -> ParseEnv tagType ct -> Parser a tagType 
lookup Z (x :: _ ) = x
lookup (S k) (_ :: xs) = lookup k xs


||| Converts a `Grammar` description into an executable Parser.
|||
||| It pattern matches on the grammar constructors and recursively builds a parser.
|||
||| @a       The type produced by the grammar.
||| @ct      The context of grammar variables (for recursive references).
||| @tagType The token tag representation used.
||| @penv    The current parser environment (a vector of previously defined parsers).
parse : {a : Type} 
     -> {ct : Vect n Type} 
     -> {tagType : Type -> Type} 
     -> {auto _ : Tag tagType} 
     -> Grammar ct a tagType 
     -> ParseEnv tagType ct 
     -> Parser a tagType
parse (MkGrammar _ (Eps g)) penv = eps g

parse (MkGrammar _ (Tok c)) penv = token c

parse (MkGrammar _ Bot) penv = bot

parse (MkGrammar _ (Seq g1 g2)) penv =
  let p1 = parse g1 penv
      p2 = parse g2 penv
  in
  seq p1 p2

parse (MkGrammar _ (Alt g1 g2)) penv = 
  let p1 = parse g1 penv 
      p2 = parse g2 penv
  in
    alt g1.lang p1 g2.lang p2

parse (MkGrammar _ (Map g f)) penv = map f $ parse g penv 

parse (MkGrammar _ (Fix g)) penv = fix (\p => parse g (p :: penv))

parse (MkGrammar _ (Var var)) penv = lookup var penv


||| Builds a parser from a fully defined grammar with no free variables.
||| Initializes `parse` with given grammanr and an empty environment.
|||
||| @a              The result type of the parser.
||| @tagType        The type of tags that token carries
||| @typedGrammar   Type checked grammar (no unbound variables).
export
generateParser : {a: Type} 
              -> {tagType : Type -> Type} 
              -> {auto _ : Tag tagType} 
              -> Grammar Nil a tagType 
              -> Parser a tagType
generateParser typedGrammar = parse typedGrammar Empty