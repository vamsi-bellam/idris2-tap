module Grammar

import Tp
import Env 

data GT : ctx -> a -> d -> Type where 
  Eps : a -> GT ctx a d
  Seq : GT ctx a d -> GT ctx b d -> GT ctx (a, b) d
  Chr : Char -> GT ctx Char d
  Bot : GT ctx a d
  Alt : GT ctx a d -> GT ctx a d -> GT ctx a d
  Map : (a -> b) -> GT ctx a d -> GT ctx b d
  Fix : GT ctx a d -> GT ctx a d
  Var : Env.Var ctx a -> GT ctx a d




typeof : Env ctx -> GT ctx a d -> Either String (TP , GT ctx a d)
typeof env (Eps y) = Right (eps, Eps y)
typeof env (Seq y z) = ?typeof_rhs_1
typeof env (Chr c) = Right (char c, Chr c)
typeof env Bot = Right (bot, Bot)
typeof env (Alt g1 g2) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof env g2
    altRes <- alt (fst g1') (fst g2') 
    Right (altRes, Alt g1 g2)

typeof env (Map f g) = 
  do  
    g' <- typeof env g 
    Right (fst g', Map f g)

typeof x (Fix y) = ?typeof_rhs_6
typeof env (Var n) = Right (lookup env n, Var n)
