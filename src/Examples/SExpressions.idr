module Examples.SExpressions

import Data.Vect
import Data.String

import Grammar
import Var
import Parser
import Token

import Examples.Utils

%hide Prelude.Ops.infixr.(<|>)

export
data SToken : Type -> Type where 
  Symbol : SToken String
  LParen : SToken () 
  RParen : SToken ()

Tag SToken where
  compare Symbol Symbol = Eql
  compare Symbol _ = Leq
  compare _ Symbol = Geq

  compare LParen LParen = Eql
  compare LParen _ = Leq
  compare _ LParen = Geq

  compare RParen RParen = Eql
  compare RParen _ = Leq
  compare _ RParen = Geq

  show Symbol = "Symbol"
  show LParen = "LParen"
  show RParen = "RParen"
  
symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (Token SToken) CharTag
symbol = word $$ (\s => (Tok Symbol (pack s)))

lparen : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (Token SToken) CharTag
lparen = char '(' $$ always (Tok LParen ())

rparen : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (Token SToken) CharTag
rparen = char ')' $$ always (Tok RParen ()) 

sexpToken : Grammar Nil (Token SToken) CharTag
sexpToken = fix sexpToken'
  where
    sexpToken' : Grammar [Token SToken] (Token SToken) CharTag
    sexpToken' = 
      any 
        [ symbol
        , lparen
        , rparen
        , skipSpace (var Z)
        ]

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

sexpression : Grammar Nil Sexp SToken
sexpression = fix sexpression'
  where
    sexpression' : Grammar [Sexp] Sexp SToken
    sexpression' = 
      (tok Symbol $$ Sym) <|>
      ((between (tok LParen) (plus (var Z)) (tok RParen)) $$ Sequence)

export 
parseSexp : String -> Either String Sexp
parseSexp input = do 
  lexedTokens <- lexer sexpToken (trim input)
  parser sexpression lexedTokens



