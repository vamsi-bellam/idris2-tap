module Examples.SExpressions

import Data.Vect

import Grammar
import Env
import Parser
import Examples.Utils


always : a -> b -> a
always x = \_ => x

export
data SToken : Type -> Type where 
  Symbol : String -> SToken String
  LParen : SToken () 
  RParen : SToken ()

symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (SToken String)
symbol = MkGrammar bot (Map (\s => Symbol (pack s)) word)

lparen : {ct : Vect n Type} -> Grammar ct (SToken ())
lparen = MkGrammar bot (Map (always LParen) (charSet "("))

rparen : {ct : Vect n Type} -> Grammar ct (SToken ())
rparen = MkGrammar bot (Map (always RParen) (charSet ")"))


public export
data Sexp = Sym String | Sequence (List Sexp)

export
Eq Sexp where
  (==) = sexpEq where 
    mutual 
      sexpEq : Sexp -> Sexp -> Bool
      sexpEq (Sym x) (Sym y) = x == y
      sexpEq (Sequence xs) (Sequence ys) = listSexpEq xs ys
      sexpEq _ _ = False

      listSexpEq : List Sexp -> List Sexp -> Bool
      listSexpEq [] [] = True
      listSexpEq (x :: xs) (y :: ys) = sexpEq x y && listSexpEq xs ys
      listSexpEq _ _ = False

export
paren : {ct : Vect n Type} -> Grammar ct a -> Grammar ct a
paren p = 
  MkGrammar 
    bot 
    (Map 
      (\((_, a), _) => a) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq lparen p)) rparen)))


atom : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (SToken String)
atom = 
  MkGrammar 
    bot 
    (Map 
      (\(first, rest) => Symbol (pack (first :: rest)))
      (MkGrammar 
        bot 
        (Seq (any [lower, upper]) (star (any [lower, upper, digit])))))

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
          (MkGrammar bot (Map (\(Symbol s) => Sym s) (wekeanGrammar symbol))) 
          (MkGrammar 
            bot 
            (Map 
              (\s => Sequence s) 
              (paren (star (MkGrammar bot (Var Z)))))))

export 
parseSexp : String -> Either String (Sexp, List Char)
parseSexp input = 
  do
    parser <- generateParser sexp 
    parser (unpack input)

