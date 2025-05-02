module Examples.Utils

import Data.Vect

import Grammar
import Parser
import Token
import Var

%hide Prelude.Ops.infixr.(<|>)

-- Reduced API from First Order to reduce verbosity

export
eps : {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> a
   -> Grammar ct a tagType
eps v = MkGrammar bot (Eps v)

export
bot : {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> Grammar ct a tagType
bot = MkGrammar bot Bot

export
tok : {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> (tagType a)
   -> Grammar ct a tagType
tok tag = MkGrammar bot (Tok tag)

export 
infixl 6 <|> 
export
(<|>) : {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> Grammar ct a tagType
   -> Grammar ct a tagType
   -> Grammar ct a tagType
(<|>) a b = MkGrammar bot (Alt a b)


export
infixl 6 >>> 
export
(>>>) : {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> Grammar ct a tagType
   -> Grammar ct b tagType
   -> Grammar ct (a, b) tagType
(>>>) a b = MkGrammar bot (Seq a b)

export
infixl 6 $$ 
export
($$) : {a : Type} 
   -> {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> Grammar ct a tagType
   -> (a -> b) 
   -> Grammar ct b tagType
($$) a f = MkGrammar bot (Map a f)

export
fix : {a : Type} 
   -> {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> Grammar (a :: ct) a tagType 
   -> Grammar ct a tagType
fix x = MkGrammar bot (Fix x)

export
var : {a : Type}
   -> {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> Var a ct
   -> Grammar ct a tagType
var x = MkGrammar bot (Var x)

-- End of Reduced API
export
star : {a : Type} 
    -> {n : Nat} 
    -> {ct : Vect n Type} 
    -> {tagType : Type -> Type} 
    -> {auto _ : Tag tagType} 
    -> Grammar ct a tagType 
    -> Grammar ct (List a) tagType
star g = fix (star' g)
  where
    star' : Grammar ct a tagType -> Grammar (List a :: ct) (List a) tagType
    star' g = eps [] <|> (wekeanGrammar g >>> var Z $$ (\(x, xs) => x :: xs))

export
plus : {a : Type} 
    -> {n : Nat} 
    -> {ct : Vect n Type} 
    -> {tagType : Type -> Type} 
    -> {auto _ : Tag tagType} 
    -> Grammar ct a tagType 
    -> Grammar ct (List a) tagType
plus g = (g >>> star g) $$ (\(x, xs) => x :: xs)

export
any : {ct : Vect n Type} 
   -> {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> List (Grammar ct a tagType) 
   -> Grammar ct a tagType
any gs = foldl (<|>) bot gs

export
always : a -> b -> a
always x = \_ => x

export
maybe : {a : Type} 
     -> {tok : Type -> Type} 
     -> {auto _ : Tag tok} 
     -> {ct : Vect n Type} 
     -> Grammar ct a tok 
     -> Grammar ct (Maybe a) tok
maybe p = any [p $$ Just, eps Nothing ]

export
between : {a, b, c : Type} 
       -> {ct : Vect n Type} 
       -> {tagType : Type -> Type} 
       -> {auto _ : Tag tagType} 
       -> Grammar ct a tagType 
       -> Grammar ct b tagType 
       -> Grammar ct c tagType
       -> Grammar ct b tagType
between left p right = (left >>> p >>> right) $$ (\((_, b), _) => b)


-- Basic helper parsers 

export
data CharTag : Type -> Type where 
  CT : Char -> CharTag Char

public export
Tag CharTag where 
  compare (CT x) (CT y) = 
    case (compare x y) of 
      LT => Leq
      EQ => Eql
      GT => Geq

  show (CT c) = show c 

export
toTokens : String -> (List (Token CharTag))
toTokens input = toTokens' (unpack input) where 
  toTokens' : List Char -> (List (Token CharTag))
  toTokens' [] = []
  toTokens' (x :: xs) = Tok (CT x) x :: (toTokens' xs)
  
export
char : {ct : Vect n Type} -> Char -> Grammar ct Char CharTag
char c = tok (CT c) $$ always c

export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char CharTag
charSet str =  charSet' (unpack str)
  where
    charSet' : List Char -> Grammar ct Char CharTag
    charSet' [] = bot
    charSet' (x :: xs) = char x <|> charSet' xs

-- Considering Only Basic Latin (ASCII)	- Letters, digits, symbols
export
compCharSet : {ct : Vect n Type} -> String -> Grammar ct Char CharTag
compCharSet s = 
  let chs = map cast (unpack s)
      predicate = filter (\x => (not (elem x chs))) [0..127]
  in charSet $ pack $ map cast predicate 

export
digit : {ct : Vect n Type} -> Grammar ct Char CharTag
digit = charSet "0123456789"

export
lower : {ct : Vect n Type} -> Grammar ct Char CharTag
lower = charSet "abcdefghijklmnopqrstuvwxyz"

export
upper : {ct : Vect n Type} -> Grammar ct Char CharTag
upper = charSet "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

export
word : {n : Nat} -> {ct : Vect n Type}  -> Grammar ct (List Char) CharTag
word = (upper >>> star lower) $$ (\(c, cs) => c :: cs)

export
whitespace : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Char CharTag
whitespace = charSet " \t\n\r"

export
skipSpace : {a : Type} 
         -> {n : Nat} 
         -> {ct : Vect n Type} 
         -> Grammar ct a CharTag 
         -> Grammar ct a CharTag
skipSpace g = (whitespace >>> g) $$ snd


-- Helpers to generate lexed tokens and parser

export 
lexer : {a : Type} -> Grammar Nil a CharTag -> String -> Either String (List a)
lexer gram input = 
  let lexer' : List (Token CharTag) -> List a -> Either String (List a)
      lexer' tokens acc = do 
        typedGrammar <- typeCheck gram
        res <- tokens |> generateParser typedGrammar
        case (snd res) of 
              [] => Right(acc ++ [fst res])
              (rest) => lexer' (rest) (acc ++ [fst res])
  in lexer' (toTokens input) [] 

export 
parser : {a : Type} 
      -> {t : Type -> Type} 
      -> {auto _ : Tag t} 
      -> Grammar Nil a t 
      -> (List (Token t)) 
      -> Either String a
parser gram tokens = do
  typedGrammar <- typeCheck gram
  res <- tokens |> generateParser typedGrammar
  case (snd res) of 
    [] => Right (fst res)
    _ => Left ("Unable to parse entire input, remaining tokens - " 
          ++ show (snd res))