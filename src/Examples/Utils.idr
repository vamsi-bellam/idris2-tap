module Examples.Utils

import Data.Vect

import Grammar


export
always : a -> b -> a
always x = \_ => x

export
maybe : {ct : Vect n Type} -> Grammar ct a -> Grammar ct (Maybe a)
maybe p = any [
  MkGrammar bot (Map (\x => Just x) p),
  MkGrammar bot (Eps Nothing)
]

export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char
charSet str =  str |> unpack |> charSet'
  where
    charSet' : List Char -> Grammar ct Char
    charSet' [] = MkGrammar bot Bot
    charSet' (c :: cs) = 
     MkGrammar bot (Alt (MkGrammar bot (Chr c)) (charSet' cs))


-- Considering Only Basic Latin (ASCII)	- Letters, digits, symbols
export
compCharSet : {ct : Vect n Type} -> String -> Grammar ct Char
compCharSet s = 
  let chs = map cast (unpack s)
      rg = [0..127]
      flt = filter (\x => (not (elem x chs))) rg
  in charSet $ pack $ map cast flt 

export
digit : {ct : Vect n Type} -> Grammar ct Char
digit = charSet "0123456789"

export
lower : {ct : Vect n Type} -> Grammar ct Char
lower = charSet "abcdefghijklmnopqrstuvwxyz"

export
upper : {ct : Vect n Type} -> Grammar ct Char
upper = charSet "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

export
word : {n : Nat} -> {ct : Vect n Type}  -> Grammar ct (List Char)
word = 
  MkGrammar 
    bot 
    (Map (\(c, cs) => c :: cs) (MkGrammar bot (Seq upper (star lower))))

export
whitespace : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Char
whitespace = charSet " \t\n\r"

export
skipEndWS : {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> Grammar ct a 
skipEndWS g = 
  MkGrammar 
    bot 
    (Map (\(x, _) => x) (MkGrammar bot (Seq g (star whitespace))))