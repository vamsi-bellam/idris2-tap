module Examples.SExpressions

import Data.Vect

import Grammar
import Env
import Parser


export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char
charSet str =  (charSet' (unpack str))
  where
    charSet' : List Char -> Grammar ct Char
    charSet' [] = MkGrammar bot Bot
    charSet' (c :: cs) = 
     MkGrammar bot (Alt (MkGrammar bot (Chr c)) (charSet' cs))

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

always : a -> b -> a
always x = \_ => x

export
data Token = SYMBOL (List Char) | LPAREN | RPAREN

symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Token
symbol = MkGrammar bot (Map (\s => SYMBOL s) word)

lparen : {ct : Vect n Type} -> Grammar ct Token
lparen = MkGrammar bot (Map (always LPAREN) (charSet "("))

rparen : {ct : Vect n Type} -> Grammar ct Token
rparen = MkGrammar bot (Map (always RPAREN) (charSet ")"))

token : {n : Nat} -> {ct : Vect n Type} ->  Grammar ct Token
token = any [symbol, lparen, rparen]

export
data Sexp = Sym | Seqq (List Sexp)

export
paren : {ct : Vect n Type} -> Grammar ct a -> Grammar ct a
paren p = 
  MkGrammar 
    bot 
    (Map 
      (\((_, a), _) => a) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq lparen p)) rparen)))


export
sexp : Grammar Nil Sexp
sexp = 
  MkGrammar bot (Fix {a = Sexp} sexp')
  where
    sexp' : Grammar [Sexp] Sexp
    sexp' = 
      MkGrammar 
        bot 
        (Alt 
          (MkGrammar bot (Map (always Sym) (wekeanGrammar symbol))) 
          (MkGrammar 
            bot 
            (Map 
              (\s => Seqq s) 
              (paren (star (MkGrammar bot (Var Z)))))))


runSexp : List Char -> Either String (Sexp, List Char)
runSexp input = 
  do
    parser <- generateParser sexp 
    parser input
