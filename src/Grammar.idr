module Grammar

import Language
import Data.Vect

mutual
  public export
  data GrammarType : (n : Nat) -> (a : Type) -> Type where 
    Eps : a -> GrammarType n a
    Seq : Grammar n a -> Grammar n b -> GrammarType n (a, b)
    Chr : Char -> GrammarType n Char
    Bot : GrammarType n a
    Alt : Grammar n a  -> Grammar n a -> GrammarType n a
    Map : (a -> b) -> Grammar n a -> GrammarType n b
    Fix : Grammar (S n) a  -> GrammarType n a
    Var : {n : Nat} -> Fin n -> GrammarType n a

  public export
  record Grammar (n : Nat) (a : Type) where
    constructor MkGrammar 
    lang : LangType
    gram : GrammarType n a



-- TODO : \{show gram} throwing error

public export
Show (Grammar n a) where 
  show (MkGrammar lang gram) = 
    """
    { lang = \{show lang}
    , gram = <grammar>
    }
    """

public export
Show a => Show (Grammar.GrammarType n a) where
  show (Eps x) = "Eps \{show x}"
  show (Seq x y) = "Seq \{show x} \{show y}"
  show (Chr c) = "Chr \{show c}"
  show Bot = "Bot"
  show (Alt x y) = "Alt \{show x} \{show y}"
  show (Map f x) = "Map <func> \{show x}"
  show (Fix x) = "Fix \{show x}"
  show (Var x) = "Var \{show x}"


addGaurd : LangType -> LangType
addGaurd lt = {guarded := True} lt

public export
typeof : {n : Nat} -> (env : Vect n LangType) -> Grammar n a -> Either String (Grammar n a)
typeof env (MkGrammar _ (Eps x)) = Right (MkGrammar eps (Eps x))

typeof env (MkGrammar _ (Seq g1 g2)) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof (map addGaurd env) g2
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


