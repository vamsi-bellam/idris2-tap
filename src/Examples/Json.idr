module Examples.Json

import Data.Vect

import Grammar
import Env
import Parser
import Examples.Utils


maybe : {ct : Vect n Type} -> Grammar ct a -> Grammar ct (Maybe a)
maybe p = any [
  MkGrammar bot (Map (\x => Just x) p),
  MkGrammar bot (Eps Nothing)
]


data JsonToken : Type -> Type where
  TNull : JsonToken ()
  TTrue : JsonToken Bool
  TFalse : JsonToken Bool
  TDecimal : Double -> JsonToken Double
  TString : String -> JsonToken String
  TLBrace : JsonToken ()
  TRBrace : JsonToken ()
  TLBracket : JsonToken ()
  TRBracket : JsonToken ()
  TColon : JsonToken ()
  TComma : JsonToken ()

export
lbracket : {ct : Vect n Type} -> Grammar ct (JsonToken ()) 
lbracket = MkGrammar bot (Map (\_ => TLBracket) (charSet "["))

export
rbracket : {ct : Vect n Type} -> Grammar ct (JsonToken ())
rbracket = MkGrammar bot (Map (\_ => TRBracket) (charSet "]"))

export
lbrace : {ct : Vect n Type} -> Grammar ct (JsonToken ())
lbrace = MkGrammar bot (Map (\_ => TLBrace) (charSet "{"))

export
rbrace : {ct : Vect n Type} -> Grammar ct (JsonToken ())
rbrace = MkGrammar bot (Map (\_ => TRBrace) (charSet "}"))

export
comma : {ct : Vect n Type} -> Grammar ct (JsonToken ())
comma = MkGrammar bot (Map (\_ => TComma) (charSet ","))

export
colon : {ct : Vect n Type} -> Grammar ct (JsonToken ())
colon = MkGrammar bot (Map (\_ => TColon) (charSet ":"))


export
nullp : {ct : Vect n Type} -> Grammar ct (JsonToken ())
nullp = 
  MkGrammar bot 
  (Map (\_ => TNull) 
    (MkGrammar bot 
      (Seq 
        (charSet "n") 
        (MkGrammar bot 
          (Seq (charSet "u") 
            (MkGrammar bot (Seq (charSet "l") (charSet "l"))))))))

export
truep : {ct : Vect n Type} -> Grammar ct (JsonToken Bool)
truep = 
  MkGrammar bot 
  (Map (\_ => TTrue) 
    (MkGrammar bot 
      (Seq 
        (charSet "t") 
        (MkGrammar bot 
          (Seq (charSet "r") 
            (MkGrammar bot (Seq (charSet "u") (charSet "e"))))))))

export
falsep : {ct : Vect n Type} -> Grammar ct (JsonToken Bool)
falsep = 
  MkGrammar bot 
  (Map (\_ => TFalse) 
    (MkGrammar bot 
      (Seq 
        (charSet "f") 
        (MkGrammar bot 
          (Seq (charSet "a") 
            (MkGrammar bot 
              (Seq (charSet "l") 
                (MkGrammar bot (Seq (charSet "s") (charSet "e"))))))))))

export
fullstringp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (JsonToken String)
fullstringp = 
  MkGrammar bot
  (Map (\((_, s), _) => TString (pack s)) 
   (MkGrammar bot 
    (Seq 
      (MkGrammar bot (Seq (charSet "\"") (star (compCharSet "\"")))) 
      (charSet "\"") )))


export
stringp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (JsonToken String)
stringp = 
  MkGrammar bot
  (Map (\((_, s), _) => TString (pack s)) 
   (MkGrammar bot 
    (Seq 
      (MkGrammar bot (Seq (charSet "\"") (star (any [lower, upper, digit])))) 
      (charSet "\"") )))

export
decimal : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (JsonToken Double)
decimal = 
  MkGrammar 
    bot
    (Map 
      toDecimal 
      (MkGrammar 
        bot 
        (Seq 
          (plus digit) 
          (maybe (MkGrammar bot (Seq (charSet ".") (plus digit)))))))
  where 
    toDecimal : (List Char, Maybe (Char, List Char)) -> JsonToken Double
    toDecimal (num, Nothing) = TDecimal (cast $ pack num)
    toDecimal (num, (Just (dot, frac))) = 
      TDecimal (cast $ pack (num ++ [dot] ++ frac))
    

export
between : {ct : Vect n Type} -> Grammar ct a -> Grammar ct b  -> Grammar ct c
        -> Grammar ct b
between left p right = 
  MkGrammar 
    bot 
    (Map 
      (\((_, b), _) => b) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq left p)) right)))

public export
data JsonValue = 
    JNull
  | JBool Bool
  | JDecimal Double
  | JString String
  | JArray (List JsonValue)
  | JObject (List (String, JsonValue))

export
Eq JsonValue where
  (==) = jsonEq where 
    mutual 
      jsonEq : JsonValue -> JsonValue -> Bool
      jsonEq JNull JNull = True
      jsonEq (JBool x) (JBool y) = x == y
      jsonEq (JDecimal x) (JDecimal y) = x == y
      jsonEq (JString x) (JString y) = x == y
      jsonEq (JArray xs) (JArray ys) = listJsonEq xs ys
      jsonEq (JObject xs) (JObject ys) = objectJsonEq xs ys
      jsonEq _ _ = False

      listJsonEq : List JsonValue -> List JsonValue -> Bool
      listJsonEq [] [] = True
      listJsonEq (x :: xs) (y :: ys) = jsonEq x y && listJsonEq xs ys
      listJsonEq _ _ = False

      objectJsonEq : List (String, JsonValue) -> List (String, JsonValue) -> Bool
      objectJsonEq [] [] = True
      objectJsonEq ((key1, value1) :: xs) ((key2, value2) :: ys) 
        = key1 == key2 && jsonEq value1 value2 && objectJsonEq xs ys
      objectJsonEq _ _ = False

export
sepByComma : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> 
        Grammar ct (List a)
sepByComma g = 
  MkGrammar bot (Fix {a = List a} (sepByComma' g))
  where
    sepByComma' : Grammar ct a -> Grammar (List a :: ct) (List a)
    sepByComma' g = 
      MkGrammar 
        bot 
        (Alt 
          (MkGrammar bot (Eps []))
          (MkGrammar bot 
            (Map 
              (\(x, xs) => case xs of 
                                Nothing => [x]
                                Just(_, rest) => x :: rest) 
              (MkGrammar 
                bot 
                (Seq 
                  (wekeanGrammar g)
                  (maybe (MkGrammar 
                            bot 
                            (Seq comma (MkGrammar bot (Var Z))))))))))


                          
member : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> 
        Grammar ct (String, a)
member x = 
  MkGrammar 
    bot 
    (Map 
      (\((TString key, _), val) => (key, val)) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq fullstringp  colon)) x)))

value :  Grammar Nil JsonValue
value = MkGrammar bot (Fix {a = JsonValue} value')
  where
    value' : Grammar [JsonValue] JsonValue
    value' = 
      let object = 
            MkGrammar 
              bot 
              (Map 
                (\kvpairs => JObject kvpairs) 
                (between 
                  lbrace 
                  (sepByComma (member (MkGrammar bot (Var Z)))) 
                  rbrace))
          array = 
            MkGrammar 
              bot 
              (Map (\rest => JArray rest) 
                (between lbracket (sepByComma (MkGrammar bot (Var Z))) rbracket))
          decimal = MkGrammar bot (Map (\(TDecimal db) => JDecimal db ) decimal)
          string = MkGrammar bot (Map (\(TString s) => JString s )  fullstringp )
          null = MkGrammar bot (Map (\_ => JNull ) nullp)
          true = MkGrammar bot (Map (\_ => JBool True ) truep)
          false = MkGrammar bot (Map (\_ => JBool False ) falsep) in 
        any [object, array, decimal, string, null, true, false]


export 
parseJSON : String -> Either String (JsonValue, List Char)
parseJSON input = 
  do
    parser <- generateParser value 
    parser (unpack input)