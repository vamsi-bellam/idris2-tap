module Grammar

import Data.Vect

import Language
import Var
import Token

mutual
  public export
  data GrammarType : {n : Nat} 
                  -> (ct : Vect n Type) 
                  -> (a : Type) 
                  -> (tagType : Type -> Type) 
                  -> Type 
    where 
      Eps : a -> GrammarType ct a tagType

      Seq : Grammar ct a tagType 
         -> Grammar ct b tagType 
         -> GrammarType ct (a, b) tagType

      Tok : tagType a -> GrammarType ct a tagType

      Bot : GrammarType ct a tagType

      Alt : Grammar ct a tagType 
         -> Grammar ct a tagType 
         -> GrammarType ct a tagType

      Map : {a : Type} 
         -> Grammar ct a tagType 
         -> (a -> b) 
         -> GrammarType ct b tagType

      Fix : {a : Type} 
         -> Grammar (a :: ct) a tagType 
         -> GrammarType ct a tagType

      Var : Var a ct -> GrammarType ct a tagType

  public export
  record Grammar (ct : Vect n Type) (a : Type) (tagType : Type -> Type) where
    constructor MkGrammar 
    lang : LangType (TokenType tagType)
    gram : GrammarType ct a tagType

mutual
  export
  showGrammar : {auto _ : Show (TokenType tagType)} 
             -> (Grammar n a tagType) 
             -> String
  showGrammar (MkGrammar lang gram) = 
    """
    { lang = "\{Prelude.show lang}"
    , gram = \{showGrammarType gram}
    }
    """

  export
  showGrammarType : {auto _ : Show (TokenType tagType)} 
                 -> (GrammarType n a tagType) 
                 -> String
  -- Ideally, need to show x too, but that requires a to have Show interface 
  -- implemented and have that constraint at the type level.
  showGrammarType (Eps x) = "Eps <base_type>"
  showGrammarType (Seq x y) = "Seq \{showGrammar x} \{showGrammar y}"
  showGrammarType (Tok c) = "Tok "
  showGrammarType Bot = "Bot"
  showGrammarType (Alt x y) = "Alt \{showGrammar x} \{showGrammar y}"
  showGrammarType (Map x f) = "Map \{showGrammar x} <func>"
  showGrammarType (Fix x) = "Fix \{showGrammar x}"
  showGrammarType (Var x) = "Var \{show x}"

mutual 
  export
  Show a => Show (TokenType tagType) => Show (Grammar n a tagType) where 
    show = showGrammar

  export
  Show a => Show (TokenType tagType) => Show (GrammarType n a tagType) where
    show = showGrammarType


addGaurd : LangType tokenType -> LangType tokenType
addGaurd lt = {guarded := True} lt

varToFin : {ct : Vect n Type} -> Var a ct -> Fin n
varToFin Z = FZ
varToFin (S x) = FS (varToFin x)

export
typeof : {a : Type } 
      -> {ct : Vect n Type} 
      -> {tagType : Type -> Type} 
      -> {auto _ : Tag tagType} 
      -> (env : Vect n (LangType (TokenType tagType)))
      -> Grammar ct a tagType 
      -> Either String (Grammar ct a tagType)

typeof env (MkGrammar  _ (Eps x)) = Right (MkGrammar eps (Eps x))

typeof env (MkGrammar  _ (Seq g1 g2)) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof (map addGaurd env) g2
    seqRes <- seq (g1'.lang) (g2'.lang) 
    Right (MkGrammar seqRes (Seq g1' g2'))

typeof env (MkGrammar _ (Tok c)) = Right (MkGrammar (tok (TokType c)) (Tok c))

typeof env (MkGrammar _ Bot) = Right (MkGrammar bot Bot)

typeof env (MkGrammar _ (Alt g1 g2)) = 
  do 
    g1' <- typeof env g1 
    g2' <- typeof env g2
    altRes <- alt (g1'.lang) (g2'.lang) 
    Right (MkGrammar altRes (Alt g1' g2'))

typeof env (MkGrammar _ (Map g f)) = 
  do  
    g' <- typeof env g 
    Right (MkGrammar g'.lang (Map g' f))

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

typeof env (MkGrammar _ (Var x)) = 
  Right (MkGrammar (index (varToFin x) env) (Var x))

export
typeCheck : {a : Type} 
         -> {tagType : Type -> Type} 
         -> {auto _ : Tag tagType} 
         -> Grammar Nil a tagType 
         -> Either String (Grammar Nil a tagType)
typeCheck gram = typeof [] gram


extendedFn : {m, n : Nat} -> (f : Fin m -> Fin n) -> Fin (S m) -> Fin (S n)
extendedFn f FZ = FZ 
extendedFn f (FS i) = FS (f i)  

extendedPrf : {ct : Vect m Type} -> {ct' : Vect n Type} -> {a : Type} ->
              (prf : (i : Fin m) -> index i ct = index (f i) ct') ->
              (i : Fin (S m)) ->
              index i (a :: ct) = index (extendedFn f i) (a :: ct')
extendedPrf prf FZ = Refl
extendedPrf prf (FS i) = prf i


varFromFin : {ct : Vect n Type} 
          -> (i : Fin n) 
          -> {auto prf : index i ct = a} 
          -> Var a ct
varFromFin {ct = a :: rest} FZ {prf = Refl} = Z
varFromFin {ct = _ :: rest} (FS x) {prf = prf} = S $ varFromFin x {prf}

evidenceOfTypeInVar : {ct : Vect n Type} 
                   -> (var : Var a ct) 
                   -> index (varToFin var) ct = a
evidenceOfTypeInVar {ct = (a :: rest)} Z = Refl
evidenceOfTypeInVar {ct = (b :: rest)} (S x) = evidenceOfTypeInVar x

reindexVar : {ct1 : Vect m Type} 
          -> {ct2 : Vect n Type} 
          -> Var h ct1 
          -> (f : Fin m -> Fin n) 
          -> (prf : (i : Fin m) 
          -> index i ct1 = index (f i) ct2) 
          -> Var h ct2
reindexVar var f prf = 
  let hIsInCt1 = evidenceOfTypeInVar var 
      hIsInCt2 = trans (sym (prf (varToFin var))) hIsInCt1 in
  varFromFin (f (varToFin var))

export
mapGrammar : {m, n : Nat} 
          -> {ct1 : Vect m Type} 
          -> {ct2 : Vect n Type} 
          -> (f : Fin m -> Fin n) 
          -> (prf : (i : Fin m) 
          -> index i ct1 = index (f i) ct2) 
          -> Grammar ct1 k tagType 
          -> Grammar ct2 k tagType
mapGrammar f prf (MkGrammar l g) = MkGrammar l (mapGramType f prf g)
  where
    mapGramType : {m, n : Nat} 
               -> {ct1 : Vect m Type} 
               -> {ct2 : Vect n Type} 
               -> (f : Fin m -> Fin n) 
               -> (prf : (i : Fin m) 
               -> index i ct1 = index (f i) ct2) 
               -> GrammarType ct1 h tagType 
               -> GrammarType ct2 h tagType

    mapGramType f prf (Eps x) = Eps x
    mapGramType f prf (Seq g1 g2) = 
      Seq (mapGrammar f prf g1) (mapGrammar f prf g2)
      
    mapGramType f prf (Tok c) = Tok c
    mapGramType f prf Bot = Bot
    mapGramType f prf (Alt g1 g2) = 
      Alt (mapGrammar f prf g1) (mapGrammar f prf g2)

    mapGramType f prf (Map g fn) = Map (mapGrammar f prf g) fn
    mapGramType f prf (Fix {a = l} {ct = bt} g) = 
      Fix (mapGrammar (extendedFn f) (extendedPrf prf) g)
    mapGramType f prf (Var v) = Var (reindexVar v f prf)


export
wekeanGrammar : {z : Type} 
             -> {m : Nat} 
             -> {ct : Vect m Type} 
             -> Grammar ct k tagType 
             -> Grammar (z :: ct) k tagType
wekeanGrammar = mapGrammar f prf
  where 
    f : Fin m -> Fin (S m)
    f i = FS i 
    prf : (i : Fin m) -> index i ct = index (f i) (z :: ct)
    prf i = Refl

export
bot : {tagType : Type -> Type} 
   -> {auto _ : Tag tagType} 
   -> LangType (TokenType tagType)
bot = Language.bot


