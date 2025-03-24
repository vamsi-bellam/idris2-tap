module Examples.Utils

import Data.Vect

import Grammar


export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char
charSet str =  str |> unpack |> charSet'
  where
    charSet' : List Char -> Grammar ct Char
    charSet' [] = MkGrammar bot Bot
    charSet' (c :: cs) = 
     MkGrammar bot (Alt (MkGrammar bot (Chr c)) (charSet' cs))


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