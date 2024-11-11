module Grammar

import Language
import Data.Vect

mutual
  public export
  data GT : (n : Nat) -> (a : Type) -> Type where 
    Eps : a -> GT n a
    Seq : Grammar n a -> Grammar n b -> GT n (a, b)
    Chr : Char -> GT n Char
    Bot : GT n a
    Alt : Grammar n a  -> Grammar n a -> GT n a
    Map : (a -> b) -> Grammar n a -> GT n b
    Fix : Grammar (S n) a  -> GT n a
    Var : {n : Nat} -> Fin n -> GT n a

  public export
  record Grammar (n : Nat) (a : Type) where
    constructor MkGrammar 
    lang : LangType
    gram  : GT n a

applyGuard : LangType -> LangType
applyGuard lt = {guarded := True} lt

mapEnv : Vect n LangType -> Vect n LangType
mapEnv env = (map applyGuard env)


public export
typeof : {n : Nat} -> (env : Vect n LangType) -> Grammar n a -> Either String (Grammar n a)
typeof env (MkGrammar _ (Eps x)) = Right (MkGrammar eps (Eps x))

typeof env (MkGrammar _ (Seq g1 g2)) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof (mapEnv env) g2
    seqRes <- seq (g1'.lang) (g2'.lang) 
    Right (MkGrammar seqRes (Seq g1' g2'))

typeof env (MkGrammar _ (Chr c)) = Right (MkGrammar (char c) (Chr c))

typeof env (MkGrammar _ Bot) = Right (MkGrammar bot Bot)

typeof env (MkGrammar _ (Alt g1 g2)) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof env g2
    altRes <- alt (g1'.lang) (g2'.lang) 
    Right (MkGrammar altRes (Alt g1' g2'))

typeof env (MkGrammar _ (Map f g)) = 
  do  
    g' <- typeof env g 
    Right (MkGrammar g'.lang (Map f g'))

typeof env (MkGrammar _ (Fix g)) = 
  do 
    l <- fix (\lt => do
                       lt' <- lt 
                       res <- (typeof (lt' :: env) g)
                       Right (res.lang))
    (if (not l.guarded) then Left "Error!"
     else 
      do
        g' <- typeof (l :: env) g
        Right (MkGrammar g'.lang  (Fix g')))

typeof env (MkGrammar _ (Var x)) = Right (MkGrammar (index x env) (Var x))



-- examples 
ct : Vect 2 LangType
ct = char 'a' :: char 'b' :: Nil

ex : Grammar (S Z) LangType 
ex = MkGrammar bot (Var (FZ))

t : Either String (Grammar 2 a)
t = typeof ct (MkGrammar bot (Var FZ))
