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

mutual
  public export
  showGrammar : (Grammar n a) -> String
  showGrammar (MkGrammar lang gram) = 
    """
    { lang = \{show lang}
    , gram = \{showGrammarType gram}
    }
    """

  public export
  showGrammarType : (GrammarType n a) -> String
  -- Ideally, need to show x too, but that requires a to have Show interface 
  -- implemented and have that constraint at the type level.
  showGrammarType (Eps x) = "Eps <base_type>"
  showGrammarType (Seq x y) = "Seq \{showGrammar x} \{showGrammar y}"
  showGrammarType (Chr c) = "Chr \{show c}"
  showGrammarType Bot = "Bot"
  showGrammarType (Alt x y) = "Alt \{showGrammar x} \{showGrammar y}"
  showGrammarType (Map f x) = "Map <func> \{showGrammar x}"
  showGrammarType (Fix x) = "Fix \{showGrammar x}"
  showGrammarType (Var x) = "Var \{show x}"

mutual 
  public export
  Show a => Show (Grammar n a) where 
    show = showGrammar

  public export
  Show a => Show (GrammarType n a) where
    show = showGrammarType


addGaurd : LangType -> LangType
addGaurd lt = {guarded := True} lt

varToFin : {ct : Vect n Type} -> Var a ct -> Fin n
varToFin Z = FZ
varToFin (S x) = FS (varToFin x)

public export
typeof : (env : Vect n LangType) ->  {ct : Vect n Type} -> Grammar ct a 
        -> Either String (Grammar ct a)
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
    (if (not l.guarded) then (Left "Error!")
     else 
      do
        g' <- typeof (l :: env) g
        Right (MkGrammar g'.lang  (Fix g')))

typeof env (MkGrammar _ (Var x)) = Right (MkGrammar (index (varToFin x) env) (Var x))

export
typeCheck : Grammar Nil a -> Either String (Grammar Nil a)
typeCheck g = typeof [] g


-- Examples 
weakenGrammar : {z : Type} -> {ct : Vect len Type} -> Grammar ct k 
                -> Grammar (z :: ct) k
weakenGrammar (MkGrammar l g) = MkGrammar l (weakenGramType g)
  where 
    weakenGramType : {z : Type} -> {ct : Vect len Type} -> GrammarType ct h 
                      -> GrammarType (z :: ct) h
    weakenGramType (Eps x) = Eps x
    weakenGramType (Seq g1 g2) = Seq (weakenGrammar g1) (weakenGrammar g2)
    weakenGramType (Chr c) = Chr c
    weakenGramType Bot = Bot
    weakenGramType (Alt g1 g2) = Alt (weakenGrammar g1) (weakenGrammar g2)
    weakenGramType (Map f g) = Map f (weakenGrammar g)
    weakenGramType (Fix {a = l} {ct = bt} g) = ?kkk
    weakenGramType (Var v) = Var (S v) 

export
star : {a : Type} -> {ct : Vect n Type} -> Grammar ct a -> Grammar ct (List a)
star g = 
  MkGrammar bot (Fix {a = List a} (star' g))
  where
    star' : Grammar ct a -> Grammar (List a :: ct) (List a)
    star' g = 
      MkGrammar bot 
        (Alt 
          (MkGrammar bot (Eps []))
          (MkGrammar bot 
            (Map (\(x, xs) => x :: xs) 
              (MkGrammar bot 
                (Seq 
                  (weakenGrammar g)
                  (MkGrammar bot (Var Z))
                )))))

export
plus : {a : Type} -> {ct : Vect n Type} -> Grammar ct a -> Grammar ct (List a)
plus g = MkGrammar bot 
          (Map (\(x, xs) => x :: xs) 
            (MkGrammar bot (Seq g (star g))))


export
charSet : String -> Grammar ct Char
charSet str =  (charSet' (unpack str))
  where
    charSet' : List Char -> Grammar ct Char
    charSet' [] = MkGrammar bot Bot
    charSet' (c :: cs) = 
     MkGrammar bot (Alt (MkGrammar bot (Chr c)) (charSet' cs))

export
lower :  Grammar Nil Char
lower = charSet "abcdefghijklmnopqrstuvwxyz"

export
upper : Grammar Nil Char
upper = charSet "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

export
lu : Grammar Nil Char 
lu = MkGrammar bot (Alt lower upper)

export 
ex : Grammar Nil (List Char)
ex = MkGrammar bot (Alt (star lower) (MkGrammar bot (Map (\x => [x]) upper)))

