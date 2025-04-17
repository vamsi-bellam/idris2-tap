module Examples.SExpressions

import Data.Vect
import Data.String

import Grammar
import Env
import Parser
import Examples.Utils
import Token

export
data SToken : Type -> Type where 
  Symbol : SToken String
  LParen : SToken () 
  RParen : SToken ()

Tag SToken where
  compare Symbol Symbol = Eql
  compare LParen LParen = Eql
  compare RParen RParen = Eql
  compare Symbol LParen = Leq
  compare Symbol RParen = Leq
  compare LParen Symbol = Geq
  compare LParen RParen = Leq
  compare RParen Symbol = Geq
  compare RParen LParen = Geq


  print Symbol = "Symbol"
  print LParen = "LParen"
  print RParen = "RParen"
  
symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (Token SToken) CharTag
symbol = MkGrammar bot (Map (\s => (Tok Symbol (pack s))) (skipEndWS word))

lparen : {ct : Vect n Type} -> Grammar ct (Token SToken) CharTag
lparen = MkGrammar bot (Map (\_ => Tok LParen ()) (charSet "("))

rparen : {ct : Vect n Type} -> Grammar ct (Token SToken) CharTag
rparen = MkGrammar bot (Map (\_ => Tok RParen ()) (charSet ")"))

lexer : Grammar Nil (List (Token SToken)) CharTag
lexer = star (any [lparen, symbol, rparen])

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
paren : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a SToken -> Grammar ct a SToken
paren p = 
  MkGrammar 
    bot 
    (Map 
      (\((_, a), _) => a) 
      (MkGrammar
        bot 
        (Seq 
          (MkGrammar bot (Seq (MkGrammar bot (Chr LParen)) p)) 
          (MkGrammar bot (Chr RParen)))))


export
sexp2 : Grammar Nil Sexp SToken
sexp2 = 
  MkGrammar bot (Fix {a = Sexp} sexp2')
  where
    sexp2' : Grammar [Sexp] Sexp SToken
    sexp2' = 
      MkGrammar 
        bot 
        (Alt 
          (MkGrammar bot (Map (\arg => Sym arg) (wekeanGrammar (MkGrammar bot (Chr Symbol))))) 
          (MkGrammar bot (Map (\arg2 => Sequence arg2) (paren (star (MkGrammar bot (Var Z)))))))


export 
lexSexp : String -> Either String (List (Token SToken), List (Token CharTag))
lexSexp input = 
  do
    parser <- generateParser lexer
    parser (toTokens (ltrim input))

export 
parseSexp : String -> Either String (Sexp, List (Token SToken))
parseSexp input = 
  do
    lexedTokens <- lexSexp input
    parser <- generateParser sexp2
    parser (fst lexedTokens)

