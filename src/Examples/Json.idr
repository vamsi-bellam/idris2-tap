module Examples.Json

import Data.Vect
import Data.String

import Grammar
import Env
import Parser
import Examples.Utils

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
  JNull == JNull = True
  JBool x == JBool y = x == y
  JDecimal x == JDecimal y = x == y
  JString x == JString y = x == y
  JArray xs == JArray ys = listJsonEq xs ys where 
    listJsonEq : List JsonValue -> List JsonValue -> Bool
    listJsonEq [] [] = True
    listJsonEq (x :: xs) (y :: ys) = x == y && listJsonEq xs ys
    listJsonEq _ _ = False
  JObject xs == JObject ys = objectJsonEq xs ys where
    objectJsonEq : List (String, JsonValue) -> List (String, JsonValue) -> Bool
    objectJsonEq [] [] = True
    objectJsonEq ((key1, value1) :: xs) ((key2, value2) :: ys) 
      = key1 == key2 && value1 == value2 && objectJsonEq xs ys
    objectJsonEq _ _ = False
  _ == _ = False


Interpolation Double where 
  interpolate d = cast d

export
Show JsonValue where 
  show JNull = "JNull"
  show (JBool True) = "JBool True"
  show (JBool False) = "JBool False"
  show (JDecimal dbl) = "JDecimal \{dbl}"
  show (JString str) = "JString \{str}"
  show (JArray xs) = "JArray [" ++ show' "" xs ++ "]" 
    where
      show' : String -> List JsonValue -> String
      show' acc [] = acc
      show' acc [x] = acc ++ show x
      show' acc (x :: xs) = show' (acc ++ show x ++ ", ") xs
  show (JObject xs) = "JObject {" ++ show' "" xs ++ "}" 
    where
      show' : String -> List (String, JsonValue) -> String
      show' acc [] = acc
      show' acc [(key, value)] = acc ++ key ++ " : " ++ show value
      show' acc ((key, value) :: xs) = 
        show' (acc ++ key ++ " : " ++ show value ++ ", ") xs

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
                            (Seq (skipEndWS comma) (MkGrammar bot (Var Z))))))))))


                          
member : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> 
        Grammar ct (String, a)
member x = 
  MkGrammar 
    bot 
    (Map 
      (\((TString key, _), val) => (key, val)) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq (skipEndWS fullstringp)  (skipEndWS colon))) x)))

value : Grammar Nil JsonValue
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
                  (skipEndWS lbrace) 
                  (sepByComma (member (MkGrammar bot (Var Z)))) 
                  (skipEndWS rbrace)))
          array = 
            MkGrammar 
              bot 
              (Map (\rest => JArray rest) 
                (between (skipEndWS lbracket) (sepByComma (MkGrammar bot (Var Z))) (skipEndWS rbracket)))
          decimal = MkGrammar bot (Map (\(TDecimal db) => JDecimal db ) (skipEndWS decimal))
          string = MkGrammar bot (Map (\(TString s) => JString s )  (skipEndWS fullstringp) )
          null = MkGrammar bot (Map (\_ => JNull ) (skipEndWS nullp))
          true = MkGrammar bot (Map (\_ => JBool True ) (skipEndWS truep))
          false = MkGrammar bot (Map (\_ => JBool False ) (skipEndWS falsep)) in 
        any [object, array, decimal, string, null, true, false]

export 
parseJSON : String -> Either String (JsonValue, List Char)
parseJSON input = 
  do
    parser <- generateParser value
    parser (unpack (ltrim input))