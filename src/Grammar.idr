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

extendedFn : {m, n : Nat} -> (f : Fin m -> Fin n) -> Fin (S m) -> Fin (S n)
extendedFn f FZ = FZ 
extendedFn f (FS i) = FS (f i)  

extendedPrf : {ct : Vect m Type} -> {ct' : Vect n Type} -> {a : Type} ->
             (prf : (i : Fin m) -> index i ct = index (f i) ct') ->
             (i : Fin (S m)) -> index i (a :: ct) = index (extendedFn f i) (a :: ct')
extendedPrf prf FZ = Refl
extendedPrf prf (FS i) = prf i


varFromFin : {ctx : Vect n Type} -> (i : Fin n) -> index i ctx = ty -> Var ty ctx
varFromFin {ctx = ty :: rest} FZ Refl = Z
varFromFin {ctx = _ :: rest} (FS x) prf = S (varFromFin x prf)

whereH : {ct1 : Vect m Type} -> (g : Var h ct1) -> (index (varToFin g) ct1 = h)
whereH {ct1 = (h :: rest)} Z = Refl
whereH {ct1 = (b :: rest)} (S x) = whereH x

reindexVar : {ct1 : Vect m Type} -> {ct2 : Vect n Type} -> 
              (given: Var h ct1) ->
             (f : Fin m -> Fin n) -> 
             (prf : (i : Fin m) -> index i ct1 = index (f i) ct2) ->  
             Var h ct2
reindexVar g f prf = 
  let fnd = whereH g in 
  varFromFin (f (varToFin g)) (sym (trans (sym fnd) (prf (varToFin g))))


partial
mapGrammar : {m, n : Nat} -> {ct1 : Vect m Type} -> {ct2 : Vect n Type} -> 
            (f : Fin m -> Fin n) -> 
            (prf : (i : Fin m) -> index i ct1 = index (f i) ct2) -> 
            Grammar ct1 k -> Grammar ct2 k
mapGrammar f prf (MkGrammar l g) = MkGrammar l (mapGramType f prf g)
  where
    mapGramType : {m, n : Nat} -> {ct1 : Vect m Type} -> {ct2 : Vect n Type} -> 
                 (f : Fin m -> Fin n) -> 
                 (prf : (i : Fin m) -> index i ct1 = index (f i) ct2) -> 
                 GrammarType ct1 h -> GrammarType ct2 h
    mapGramType f prf (Eps x) = Eps x
    mapGramType f prf (Seq g1 g2) = Seq (mapGrammar f prf g1) (mapGrammar f prf g2)
    mapGramType f prf (Chr c) = Chr c
    mapGramType f prf Bot = Bot
    mapGramType f prf (Alt g1 g2) = Alt (mapGrammar f prf g1) (mapGrammar f prf g2)
    mapGramType f prf (Map fn g) = Map fn (mapGrammar f prf g)
    mapGramType f prf (Fix {a = l} {ct = bt} g) = 
      Fix (mapGrammar (extendedFn f) (extendedPrf prf) g)
    mapGramType f prf (Var v) = Var (reindexVar v f prf)


wekeanGrammar : {z : Type} -> {m : Nat} -> {ct : Vect m Type} -> Grammar ct k -> Grammar (z :: ct) k
wekeanGrammar = mapGrammar f prf
  where 
    f : Fin m -> Fin (S m)
    f i = FS i 
    prf : (i : Fin m) -> index i ct = index (f i) (z :: ct)
    prf i = Refl

-- Examples 
export
star : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> Grammar ct (List a)
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
                  (wekeanGrammar g)
                  (MkGrammar bot (Var Z))
                )))))

export
plus : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> Grammar ct (List a)
plus g = MkGrammar bot 
          (Map (\(x, xs) => x :: xs) 
            (MkGrammar bot (Seq g (star g))))

any : List (Grammar Nil a) -> Grammar Nil a
any lg = foldl (\g1, g2 => MkGrammar bot (Alt g1 g2)) (MkGrammar bot Bot) lg



export
charSet : {ct : Vect n Type} -> String -> Grammar ct Char
charSet str =  (charSet' (unpack str))
  where
    charSet' : List Char -> Grammar ct Char
    charSet' [] = MkGrammar bot Bot
    charSet' (c :: cs) = 
     MkGrammar bot (Alt (MkGrammar bot (Chr c)) (charSet' cs))

export
lower : {ct : Vect n Type} -> Grammar ct Char
lower = charSet "abcdefghijklmnopqrstuvwxyz"

export
upper : {ct : Vect n Type} -> Grammar ct Char
upper = charSet "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

export
word : {n : Nat} -> {ct : Vect n Type}  -> Grammar ct (List Char)
word = 
  MkGrammar 
    bot 
    (Map (\(c, cs) => c :: cs) (MkGrammar bot (Seq upper (star lower))))

always : a -> b -> a
always x = \_ => x

export
option : Grammar Nil a -> Grammar Nil (Maybe a)
option g = 
  MkGrammar 
    bot 
    (Alt (MkGrammar bot (Eps Nothing)) (MkGrammar bot (Map (\x => Just x) g)))

export
ex2 : Grammar Nil (Maybe Char)
ex2 = option (charSet "a")

export
data Token = SYMBOL (List Char) | LPAREN | RPAREN

symbol : {n : Nat} -> {ct : Vect n Type} -> Grammar ct Token
symbol = MkGrammar bot (Map (\s => SYMBOL s) word)

lparen : {ct : Vect n Type} -> Grammar ct Token
lparen = MkGrammar bot (Map (always LPAREN) (charSet "("))

rparen : {ct : Vect n Type} -> Grammar ct Token
rparen = MkGrammar bot (Map (always RPAREN) (charSet ")"))

token : Grammar Nil Token
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
