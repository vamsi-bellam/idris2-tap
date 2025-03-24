module Examples.SExpressions

import Data.Vect

import Grammar
import Env
import Parser
import Examples.Utils


always : a -> b -> a
always x = \_ => x

export
data Token = SYMBOL (List Char) | LPAREN | RPAREN

symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Token
symbol = MkGrammar bot (Map (\s => SYMBOL s) word)
-- symbol = 
--  MkGrammar 
--             bot 
--             (Map 
--               (\(c, cs) => SYMBOL (c :: cs)) 
--               (MkGrammar bot (Seq (upper) (star (any [lower, upper])))))
  -- MkGrammar 
  --   bot 
  --   (Alt (  MkGrammar 
  --           bot 
  --           (Map 
  --             (\(c, cs) => SYMBOL (c :: cs)) 
  --             (MkGrammar bot (Seq (lower) (star (any [lower, upper])))))) 
  --       (  MkGrammar 
  --           bot 
  --           (Map 
  --             (\(c, cs) => SYMBOL (c :: cs)) 
  --             (MkGrammar bot (Seq (upper) (star (any [lower, upper])))))))

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
