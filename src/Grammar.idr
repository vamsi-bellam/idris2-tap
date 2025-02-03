module Grammar

import Language
import Data.Vect
import Env

mutual
  public export
  data GrammarType : {n : Nat} -> (ct : Vect n Type) -> (a : Type) -> Type where 
    Eps : a -> GrammarType ct a
    Seq : Grammar ct a -> Grammar ct b -> GrammarType ct (a, b)
    Chr : Char -> GrammarType ct Char
    Bot : GrammarType ct a
    Alt : Grammar ct a -> Grammar ct a -> GrammarType ct a
    Map : (a -> b) -> Grammar ct a -> GrammarType ct b
    Fix : {a : Type} -> Grammar (a :: ct) a -> GrammarType ct a
    Var : Var a ct -> GrammarType ct a

  public export
  record Grammar (ct : Vect n Type) (a : Type) where
    constructor MkGrammar 
    lang : LangType
    gram : GrammarType ct a

-- mutual
--   public export
--   showGrammar : Show a => (Grammar n a) -> String
--   showGrammar (MkGrammar lang gram) = 
--     """
--     { lang = \{show lang}
--     , gram = \{showGrammarType gram}
--     }
--     """

--   public export
--   showGrammarType : Show a => (GrammarType n a) -> String
--   showGrammarType (Eps x) = "Eps \{show x}"
--   showGrammarType (Seq x y) = "Seq \{showGrammar x} \{showGrammar y}"
--   showGrammarType (Chr c) = "Chr \{show c}"
--   showGrammarType Bot = "Bot"
--   showGrammarType (Alt x y) = "Alt \{showGrammar x} \{showGrammar y}"
--   showGrammarType (Map f x) = "Map <func> \{showGrammar x}"
--   showGrammarType (Fix x) = "Fix \{showGrammar x}"
--   showGrammarType (Var x) = "Var \{show x}"

-- mutual 
--   public export
--   Show a => Show (Grammar n a) where 
--     show = showGrammar

--   public export
--   Show a => Show (GrammarType n a) where
--     show = showGrammarType


addGaurd : LangType -> LangType
addGaurd lt = {guarded := True} lt

vToF : {ct : Vect n Type} -> Var a ct -> Fin n
vToF Z = FZ
vToF (S x) = FS (vToF x)

public export
typeof : {n : Nat} -> (env : Vect n LangType) ->  {ct : Vect n Type} 
          -> Grammar ct a -> Either String (Grammar ct a)
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

typeof env (MkGrammar _ (Var x)) = Right (MkGrammar (index (vToF x) env) (Var x))


