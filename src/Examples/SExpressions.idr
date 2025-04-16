module Examples.SExpressions

import Data.Vect
import Data.String

import Grammar
import Env
import Parser
import Examples.Utils

export
data SToken : Type -> Type where 
  Symbol : String -> SToken String
  LParen : SToken () 
  RParen : SToken ()

public export
data Token : Type where
  Tok : {a : Type} -> Tag a -> a -> Token

  
symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (SToken String) Char
symbol = MkGrammar bot (Map (\s => Symbol (pack s)) (skipEndWS word))

lparen : {ct : Vect n Type} -> Grammar ct (SToken ()) Char
lparen = MkGrammar bot (Map (always LParen) (charSet "("))

rparen : {ct : Vect n Type} -> Grammar ct (SToken ()) Char
rparen = MkGrammar bot (Map (always RParen) (charSet ")"))

lexer2 : Grammar Nil (SToken a) Char
lexer2 = any [lparen, symbol]

public export
data Sexp = Sym String | Sequence (List Sexp)


export
Show Sexp where 
  show (Sym str) = "Sym \{str}"
  show (Sequence xs) = "Sequence [" ++ show' "" xs ++ "]" 
    where
      show' : String -> List Sexp -> String
      show' acc [] = acc
      show' acc [x] = acc ++ show x
      show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs
    

export
Eq Sexp where
  Sym x == Sym y = x == y
  Sequence xs == Sequence ys = listSexpEq xs ys
    where
      listSexpEq : List Sexp -> List Sexp -> Bool
      listSexpEq [] [] = True
      listSexpEq (x :: xs) (y :: ys) = x == y && listSexpEq xs ys
      listSexpEq _ _ = False
  _ == _ = False


export
paren : {n : Nat} -> {ct : Vect n Type} -> Grammar ct a Char -> Grammar ct a Char
paren p = 
  MkGrammar 
    bot 
    (Map 
      (\((_, a), _) => a) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq (skipEndWS lparen) p)) (skipEndWS rparen))))


export
sexp2 : Ord a => Grammar Nil Sexp a
sexp2 = 
  MkGrammar bot (Fix {a = Sexp} sexp2')
  where
    sexp2' : Grammar [Sexp] Sexp a
    sexp2' = 
      MkGrammar 
        bot 
        (Alt 
          (MkGrammar bot (Map (?lk) (wekeanGrammar ?lko))) 
          ?fill_next)


export
sexp : Grammar Nil Sexp Char
sexp = 
  MkGrammar bot (Fix {a = Sexp} sexp')
  where
    sexp' : Grammar [Sexp] Sexp Char
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
    parser (unpack (ltrim input))

