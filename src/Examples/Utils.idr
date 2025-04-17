module Examples.Utils

import Data.Vect

import Grammar
import Parser
import Token


export
always : a -> b -> a
always x = \_ => x

export
maybe : {a : Type} -> {tok : Type -> Type} -> Tag tok => {ct : Vect n Type} -> Grammar ct a tok -> Grammar ct (Maybe a) tok
maybe p = any [
  MkGrammar bot (Map (\x => Just x) p),
  MkGrammar bot (Eps Nothing)
]

public export
data CharTag : Type -> Type where 
  CT : Char -> CharTag Char

FromChar (CharTag Char) where 
  fromChar h = CT h

public export
Tag CharTag where 
  compare (CT x) (CT y) = 
    case (compare x y) of 
      LT => Leq
      EQ => Eql
      GT => Geq

  show (CT c) = show c 


public export
toTokens : String -> (List (Token CharTag))
toTokens str = toTokens' (unpack str) where 
  toTokens' : List Char -> (List (Token CharTag))
  toTokens' [] = []
  toTokens' (x :: xs) = Tok (CT x) x :: (toTokens' xs)
  

char : {ct : Vect n Type} -> Char -> Grammar ct Char CharTag
char c = MkGrammar bot (Map (\_ => c) (MkGrammar bot (Chr (CT c))))

export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char CharTag
charSet str =  charSet' (unpack str)
  where
    charSet' : List Char -> Grammar ct Char CharTag
    charSet' [] = MkGrammar bot Bot
    charSet' (x :: xs) = MkGrammar bot (Alt (char x) (charSet' xs))


-- Considering Only Basic Latin (ASCII)	- Letters, digits, symbols
export
compCharSet : {ct : Vect n Type} -> String -> Grammar ct Char CharTag
compCharSet s = 
  let chs = map cast (unpack s)
      rg = [0..127]
      flt = filter (\x => (not (elem x chs))) rg
  in charSet $ pack $ map cast flt 

export
digit : Ord tok => {ct : Vect n Type} -> Grammar ct Char CharTag
digit = charSet "0123456789"


export
lower : {ct : Vect n Type} -> Grammar ct Char CharTag
lower = charSet "abcdefghijklmnopqrstuvwxyz"

export
upper : {ct : Vect n Type} -> Grammar ct Char CharTag
upper = charSet "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

export
word : {n : Nat} -> {ct : Vect n Type}  -> Grammar ct (List Char) CharTag
word = 
  MkGrammar 
    bot 
    (Map (\(c, cs) => c :: cs) (MkGrammar bot (Seq upper (star lower))))

export
whitespace : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Char CharTag
whitespace = charSet " \t\n\r"

export
skipEndWS : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a CharTag -> Grammar ct a CharTag
skipEndWS g = 
  MkGrammar 
    bot 
    (Map (\(x, _) => x) (MkGrammar bot (Seq g (star whitespace))))

export
haveEndWs : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a CharTag -> Grammar ct a CharTag
haveEndWs g = 
  MkGrammar 
    bot 
    (Map (\(x, _) => x) (MkGrammar bot (Seq g (plus whitespace))))