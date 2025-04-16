module Examples.Utils

import Data.Vect

import Grammar
import Parser


export
always : a -> b -> a
always x = \_ => x

export
maybe : Ord tok => {ct : Vect n Type} -> Grammar ct a tok -> Grammar ct (Maybe a) tok
maybe p = any [
  MkGrammar bot (Map (\x => Just x) p),
  MkGrammar bot (Eps Nothing)
]

export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char Char
charSet str =  str |> unpack |> charSet'
  where
    charSet' : List Char -> Grammar ct Char Char
    charSet' [] = MkGrammar bot Bot
    charSet' (c :: cs) = 
     MkGrammar bot (Alt (MkGrammar bot (Chr c)) (charSet' cs))


-- Considering Only Basic Latin (ASCII)	- Letters, digits, symbols
export
compCharSet : {ct : Vect n Type} -> String -> Grammar ct Char Char
compCharSet s = 
  let chs = map cast (unpack s)
      rg = [0..127]
      flt = filter (\x => (not (elem x chs))) rg
  in charSet $ pack $ map cast flt 

export
digit : Ord tok => {ct : Vect n Type} -> Grammar ct Char Char
digit = charSet "0123456789"


-- data Tokens = LP | S String | RP

-- Show Tokens where
--   show _ = "<>show<>"

-- Eq Tokens where
--   LP == LP = True
--   (S str) == (S str2) = str == str2
--   RP == RP = True
--   _ == _ = False

-- Ord Tokens where 
--   compare LP LP = EQ
--   compare LP (S str) = GT
--   compare LP RP = GT
--   compare (S str) LP = LT
--   compare (S str) (S str1) = compare str str1
--   compare (S str) RP = GT
--   compare RP LP = LT
--   compare RP (S str) = LT
--   compare RP RP = EQ


-- export
-- s : Grammar Nil Tokens Char
-- s = MkGrammar bot (Map (\_ => LP) (charSet "("))


-- export 
-- parseSexp : String -> Either String (Tokens, List Char)
-- parseSexp input = do
--     parser <- generateParser s 
--     parser (unpack (input))


-- export
-- s' : Show Tokens => Ord Tokens => Grammar Nil Char Tokens
-- s' = MkGrammar bot (Map (\_ => 'a') (MkGrammar bot (Chr LP)))



-- export 
-- parseSexp2 : Show Tokens => List Tokens -> Either String (Char, List Tokens)
-- parseSexp2 input = do
--     parser <- generateParser s' 
--     parser (input)


export
lower : {ct : Vect n Type} -> Grammar ct Char Char
lower = charSet "abcdefghijklmnopqrstuvwxyz"

export
upper : {ct : Vect n Type} -> Grammar ct Char Char
upper = charSet "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

export
word : {n : Nat} -> {ct : Vect n Type}  -> Grammar ct (List Char) Char
word = 
  MkGrammar 
    bot 
    (Map (\(c, cs) => c :: cs) (MkGrammar bot (Seq upper (star lower))))

export
whitespace : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Char Char
whitespace = charSet " \t\n\r"

export
skipEndWS : {n : Nat} -> {ct : Vect n Type} -> Grammar ct a Char -> Grammar ct a Char
skipEndWS g = 
  MkGrammar 
    bot 
    (Map (\(x, _) => x) (MkGrammar bot (Seq g (star whitespace))))

export
haveEndWs : {n : Nat} -> {ct : Vect n Type} -> Grammar ct a Char -> Grammar ct a Char
haveEndWs g = 
  MkGrammar 
    bot 
    (Map (\(x, _) => x) (MkGrammar bot (Seq g (plus whitespace))))