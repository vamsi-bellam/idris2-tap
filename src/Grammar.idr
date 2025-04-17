module Grammar

import Language
import Data.Vect
import Env
import Token

mutual
  public export
  data GrammarType : {n : Nat} -> (ct : Vect n Type) -> (a : Type) -> (tok : Type -> Type) -> Type where 
    Eps :  a -> GrammarType ct a tok
    Seq : Grammar ct a tok -> Grammar ct b tok -> GrammarType ct (a, b) tok
    Chr : tok a -> GrammarType ct a tok
    Bot : GrammarType ct a tok
    Alt : Grammar ct a tok -> Grammar ct a tok -> GrammarType ct a tok
    Map : {a : Type} -> (a -> b) -> Grammar ct a tok -> GrammarType ct b tok
    Fix : {a : Type} -> Grammar (a :: ct) a tok -> GrammarType ct a tok
    Var : Var a ct -> GrammarType ct a tok

  public export
  record Grammar (ct : Vect n Type) (a : Type) (tok : Type -> Type) where
    constructor MkGrammar 
    lang : LangType (TokenType tok)
    gram : GrammarType ct a tok

mutual
  export
  showGrammar : (Grammar n a tok) -> String
  showGrammar (MkGrammar lang gram) = 
    """
    { lang = "<fill>"
    , gram = \{showGrammarType gram}
    }
    """

  export
  showGrammarType : (GrammarType n a tok) -> String
  -- Ideally, need to show x too, but that requires a to have Show interface 
  -- implemented and have that constraint at the type level.
  showGrammarType (Eps x) = "Eps <base_type>"
  showGrammarType (Seq x y) = "Seq \{showGrammar x} \{showGrammar y}"
  showGrammarType (Chr c) = "Chr "
  showGrammarType Bot = "Bot"
  showGrammarType (Alt x y) = "Alt \{showGrammar x} \{showGrammar y}"
  showGrammarType (Map f x) = "Map <func> \{showGrammar x}"
  showGrammarType (Fix x) = "Fix \{showGrammar x}"
  showGrammarType (Var x) = "Var \{show x}"

mutual 
  export
  Show a => Show (Grammar n a tok) where 
    show = showGrammar

  export
  Show a => Show (GrammarType n a tok) where
    show = showGrammarType


addGaurd : LangType tok -> LangType tok
addGaurd lt = {guarded := True} lt

varToFin : {ct : Vect n Type} -> Var a ct -> Fin n
varToFin Z = FZ
varToFin (S x) = FS (varToFin x)

export
typeof : {a : Type} -> Show (TokenType tok) => Ord (TokenType tok) => (env : Vect n (LangType (TokenType tok))) ->  {ct : Vect n Type} -> Grammar ct a tok 
        -> Either String (Grammar ct a tok)
typeof env (MkGrammar  _ (Eps x)) = Right (MkGrammar eps (Eps x))

typeof env (MkGrammar  _ (Seq g1 g2)) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof (map addGaurd env) g2
    seqRes <- seq (g1'.lang) (g2'.lang) 
    Right (MkGrammar seqRes (Seq g1' g2'))

typeof env (MkGrammar _ (Chr c)) = Right (MkGrammar (char (TokType c)) (Chr c))

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
typeCheck : {a : Type} -> Ord (TokenType tok) => Show (TokenType tok) => Grammar Nil a tok -> Either String (Grammar Nil a tok)
typeCheck g = typeof [] g




-- Helpers 

extendedFn : {m, n : Nat} -> (f : Fin m -> Fin n) -> Fin (S m) -> Fin (S n)
extendedFn f FZ = FZ 
extendedFn f (FS i) = FS (f i)  

extendedPrf : {ct : Vect m Type} -> {ct' : Vect n Type} -> {a : Type} ->
              (prf : (i : Fin m) -> index i ct = index (f i) ct') ->
              (i : Fin (S m)) ->
              index i (a :: ct) = index (extendedFn f i) (a :: ct')
extendedPrf prf FZ = Refl
extendedPrf prf (FS i) = prf i


varFromFin : {ct : Vect n Type} -> (i : Fin n) -> {auto prf : index i ct = a} 
              -> Var a ct
varFromFin {ct = a :: rest} FZ {prf = Refl} = Z
varFromFin {ct = _ :: rest} (FS x) {prf = prf} = S $ varFromFin x {prf}

evidenceOfTypeInVar : {ct : Vect n Type} -> (var : Var a ct) -> 
                      index (varToFin var) ct = a
evidenceOfTypeInVar {ct = (a :: rest)} Z = Refl
evidenceOfTypeInVar {ct = (b :: rest)} (S x) = evidenceOfTypeInVar x

reindexVar : {ct1 : Vect m Type} -> {ct2 : Vect n Type} -> Var h ct1 ->
             (f : Fin m -> Fin n) -> 
             (prf : (i : Fin m) -> index i ct1 = index (f i) ct2) ->  
             Var h ct2
reindexVar var f prf = 
  let hIsInCt1 = evidenceOfTypeInVar var 
      hIsInCt2 = trans (sym (prf (varToFin var))) hIsInCt1 in
  varFromFin (f (varToFin var))

export
mapGrammar : {m, n : Nat} -> {ct1 : Vect m Type} -> {ct2 : Vect n Type} -> 
            (f : Fin m -> Fin n) -> 
            (prf : (i : Fin m) -> index i ct1 = index (f i) ct2) -> 
            Grammar ct1 k tok -> Grammar ct2 k tok
mapGrammar f prf (MkGrammar l g) = MkGrammar l (mapGramType f prf g)
  where
    mapGramType : {m, n : Nat} -> {ct1 : Vect m Type} -> {ct2 : Vect n Type} -> 
                 (f : Fin m -> Fin n) -> 
                 (prf : (i : Fin m) -> index i ct1 = index (f i) ct2) -> 
                 GrammarType ct1 h tok -> GrammarType ct2 h tok
    mapGramType f prf (Eps x) = Eps x
    mapGramType f prf (Seq g1 g2) = Seq (mapGrammar f prf g1) (mapGrammar f prf g2)
    mapGramType f prf (Chr c) = Chr c
    mapGramType f prf Bot = Bot
    mapGramType f prf (Alt g1 g2) = Alt (mapGrammar f prf g1) (mapGrammar f prf g2)
    mapGramType f prf (Map fn g) = Map fn (mapGrammar f prf g)
    mapGramType f prf (Fix {a = l} {ct = bt} g) = 
      Fix (mapGrammar (extendedFn f) (extendedPrf prf) g)
    mapGramType f prf (Var v) = Var (reindexVar v f prf)


export
wekeanGrammar : {z : Type} -> {m : Nat} -> {ct : Vect m Type} -> 
                Grammar ct k tok -> Grammar (z :: ct) k tok
wekeanGrammar = mapGrammar f prf
  where 
    f : Fin m -> Fin (S m)
    f i = FS i 
    prf : (i : Fin m) -> index i ct = index (f i) (z :: ct)
    prf i = Refl

export
star : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Ord (TokenType tok) => Show (TokenType tok) => Grammar ct a tok -> 
        Grammar ct (List a) tok
star g = 
  MkGrammar bot (Fix {a = List a} (star' g))
  where
    star' : Grammar ct a tok -> Grammar (List a :: ct) (List a) tok
    star' g = 
      MkGrammar bot (Alt 
                      (MkGrammar bot (Eps []))
                      (MkGrammar bot 
                        (Map (\(x, xs) => x :: xs) 
                          (MkGrammar bot 
                            (Seq 
                              (wekeanGrammar g)
                              (MkGrammar bot (Var Z))
                            )))))

export
plus :  Ord (TokenType tok) => Show (TokenType tok) => {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a tok -> 
        Grammar ct (List a) tok
plus g = 
  MkGrammar bot (Map (\(x, xs) => x :: xs) (MkGrammar bot (Seq g (star g))))

export
any : Ord (TokenType tok) => Show (TokenType tok) => {ct : Vect n Type} -> List (Grammar ct a tok) -> Grammar ct a tok
any lg = foldl (\g1, g2 => MkGrammar bot (Alt g1 g2)) (MkGrammar bot Bot) lg

export
bot : Ord (TokenType tok) => Show (TokenType tok) => LangType (TokenType tok)
bot = Language.bot


