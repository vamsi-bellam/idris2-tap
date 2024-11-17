module Hoas

import Grammar
import Language
import Data.So
import Data.Fin
import Data.Vect


HT : Type -> Type
HT a = {n : Nat} -> Fin n -> Grammar n a

-- eps : a -> HT a
-- eps x n = MkGrammar bot (Eps x)

eps : HT ()
eps n = MkGrammar bot (Eps ())

char : Char -> HT Char
char c _ = MkGrammar bot (Chr c)

seq : HT a -> HT b -> HT (a, b)
seq f g n = MkGrammar bot (Seq (f n) (g n))

bot : HT a
bot _ = MkGrammar bot Bot

alt : HT a -> HT a -> HT a
alt f g n = MkGrammar bot (Alt (f n) (g n))

tshift : {a : Nat} -> {b : Nat} -> (j : Fin a) -> (l : Fin b) -> Fin a
tshift FZ FZ = FZ
-- Need to prove this as impossible
tshift FZ (FS x) = FZ
tshift (FS x) FZ = FS x
tshift (FS x) (FS y) = FS (tshift x y)


fix : (HT a -> HT a) -> HT a
fix f i = 
  MkGrammar 
    bot 
    (Fix ((f (\j => MkGrammar bot (Var (tshift j (FS i))))) (FS i)))

map : (a -> b) -> HT a -> HT b
map f g n = MkGrammar bot (Map f (g n))

any : List (HT a) -> HT a
any ls = foldl alt bot ls

always : a -> b -> a
always x = \_ => x

star : HT a -> HT (List a)
star g = 
  fix (\f => 
        any 
          [ map (always []) (eps) 
          , map (\(c, cs) => c :: cs) (seq g f) 
          ] 
      )


typeCheck : HT a -> Either String (Grammar 1 a)
typeCheck f = typeof [bot] (f FZ)


-- examples 

charset : String -> HT Char
charset str = any (map char (unpack str))

lower : HT Char 
lower = charset "abcdefghijklmnopqrstuvwxyz"

upper : HT Char 
upper = charset "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

word : HT (List Char)
word = map (\(c, cs) => c :: cs) (seq upper (star lower))

data Token = SYMBOL (List Char) | LPAREN | RPAREN

symbol : HT Token
symbol = map (\s => SYMBOL s) word

lparen : HT Token
lparen = map (always LPAREN) (char '(')

rparen : HT Token
rparen = map (always RPAREN) (char ')')

token : HT Token
token = any [symbol, lparen, rparen]

data Sexp = Sym | Seq (List Sexp)

paren : HT a -> HT a
paren p = map (\((_, a), _) => a) (seq (seq lparen p) rparen)

exParen : HT (List (Char, Char))
exParen = star (paren (seq (char 'a') (alt (char 'b') (char 'c')) ))

sexp : HT Sexp 
sexp = fix (\f => 
            any 
              [
                map (always Sym) symbol
              , map (\s => Seq s) (paren (star f))
              ])