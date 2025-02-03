module Hoas

import Grammar
import Language
import Data.So
import Data.Fin
import Data.Vect
import Parser2
import Decidable.Equality
import Env

public export
data PEnv : Vect n Type -> Type where
  Nil  : PEnv []
  (::) : (a : Type) -> PEnv as -> PEnv (a :: as)


HT : Type -> Type
HT a = {n : Nat} -> {ct : Vect n Type} -> PEnv ct -> Grammar ct a 

eps : HT ()
eps _ = MkGrammar bot (Eps ())

char : Char -> HT Char
char c _ = MkGrammar bot (Chr c)

seq : HT a -> HT b -> HT (a, b)
seq f g ct = MkGrammar bot (Seq (f ct) (g ct))

bot : HT a
bot _ = MkGrammar bot Bot

alt : HT a -> HT a -> HT a
alt f g ct = MkGrammar bot (Alt (f ct) (g ct))

tsh : (dlen : Nat) -> PEnv ct1 -> PEnv (a :: ct2) -> Var a ct1
tsh dlen x y = ?tsh_rhs

len : PEnv ct  -> Nat
len [] = 0
len (x :: y) = S (len y)

diff : PEnv ct1 -> PEnv ct2 -> Nat
diff c1 c2 = minus (len c1) (len c2) 
  
fix : {a : Type} -> (HT a -> HT a) -> HT a
fix f ctx = 
  let extendedCtx = (a :: ctx) in
  MkGrammar 
    bot 
    (Fix 
      ((f 
        (\ct => MkGrammar bot (Var (tsh (diff ct extendedCtx) ct extendedCtx)))
        ) extendedCtx ))


map : (a -> b) -> HT a -> HT b
map f g ct = MkGrammar bot (Map f (g ct))

any : List (HT a) -> HT a
any ls = foldl alt bot ls

always : a -> b -> a
always x = \_ => x

star : {a : Type} -> HT a -> HT (List a)
star g = 
  fix (\f => 
        any 
          [ map (always []) (eps) 
          , map (\(c, cs) => c :: cs) (seq g f) 
          ] 
      )


-- typeCheck : {ct : Vect 1 Type} -> HT a -> Either String (Grammar ct a)
-- typeCheck f = typeof [bot] (f ct) 


-- p1 : Either String  (Grammar [Char] Char)
-- p1 = typeCheck (alt (char 'a') (char 'b'))

-- ap : {a : Type} -> HT a -> Either String (Parser a)
-- ap p = do 
--         g <- typeCheck {ct = [a]} p 
--         Right (parse g (bot :: Parser2.Nil))


-- examples 

charset : String -> HT Char
charset str = any (map char (unpack str))

lower : HT Char 
lower = charset "abcdefghijklmnopqrstuvwxyz"

upper : HT Char 
upper = charset "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

-- word : HT (List Char)
-- word = map (\(c, cs) => c :: cs) (seq upper (star lower))

-- data Token = SYMBOL (List Char) | LPAREN | RPAREN

-- symbol : HT Token
-- symbol = map (\s => SYMBOL s) word

-- lparen : HT Token
-- lparen = map (always LPAREN) (char '(')

-- rparen : HT Token
-- rparen = map (always RPAREN) (char ')')

-- token : HT Token
-- token = any [symbol, lparen, rparen]

-- data Sexp = Sym | Seq (List Sexp)

-- paren : HT a -> HT a
-- paren p = map (\((_, a), _) => a) (seq (seq lparen p) rparen)

-- exParen : HT (List (Char, Char))
-- exParen = star (paren (seq (char 'a') (alt (char 'b') (char 'c')) ))

-- sexp : HT Sexp 
-- sexp = fix (\f => 
--             any 
--               [
--                 map (always Sym) symbol
--               , map (\s => Seq s) (paren (star f))
--               ])