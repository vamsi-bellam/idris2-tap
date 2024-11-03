module Grammar

import Language
import Env 
import Data.SortedSet

public export
data GT : (ctx : Type) -> (a : Type) -> Type where 
  Eps : a -> GT ctx a
  Seq : GT ctx a -> GT ctx b -> GT ctx (a, b)
  Chr : Char -> GT ctx Char
  Bot : GT ctx a
  Alt : GT ctx a -> GT ctx a -> GT ctx a
  Map : (a -> b) -> GT ctx a -> GT ctx b
  Fix : GT (LangType, ctx) a -> GT ctx a
  Var : Env.Var ctx LangType -> GT ctx a

public export 
record GType ctx a where 
  constructor MkGType
  d : LangType
  g : GT ctx a

fn : LangType -> LangType
fn lt = {guarded := True} lt

public export
typeof : Env ctx -> GT ctx a -> Either String (LangType , GT ctx a)
typeof env (Eps y) = Right (eps, Eps y)
typeof env (Seq g1 g2) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof (map (?lk) env) g2
    seqRes <- seq (fst g1') (fst g2') 
    Right (seqRes, Seq (snd g1') (snd g2'))

typeof env (Chr c) = Right (char c, Chr c)
typeof env Bot = Right (bot, Bot)
typeof env (Alt g1 g2) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof env g2
    altRes <- alt (fst g1') (fst g2') 
    Right (altRes, Alt (snd g1') (snd g2'))

typeof env (Map f g) = 
  do  
    g' <- typeof env g 
    Right (fst g', Map f (snd g'))

typeof env (Fix g) = 
  do 
    l <- fix (\lt => do
                       lt' <- lt 
                       res <- (typeof (lt' :: env) g)
                       Right (fst res))
    (if (not l.guarded) then Left "Error!"
     else 
      do
        g' <- typeof (l :: env) g
        Right (fst g', Fix (snd g')))
typeof env (Var n) = Right (lookup env n, Var n)





--- Examples --- 

first : Var (LangType, ctx) LangType
first = Z

sec : Var (LangType, (LangType, ctx)) LangType
sec = S first

testEnv : Env (LangType, ())
testEnv = char 'a' ::
          Nil

gg : GT (LangType, ctx) LangType
gg = Var Z