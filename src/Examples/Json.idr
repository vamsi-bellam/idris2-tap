module Examples.Json

import Data.Vect

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
stringp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (JsonToken String)
stringp = 
  MkGrammar bot
  (Map (\((_, s), _) => TString (pack s)) 
   (MkGrammar bot 
    (Seq 
      (MkGrammar bot (Seq (charSet "\"") (star (any [lower, upper])))) 
      (charSet "\"") )))

export
decimal : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (JsonToken Double)
decimal = 
  MkGrammar bot
  (Map (\((s, d), e) => TDecimal (cast (pack (s ++ [d] ++ e) ))) 
   (MkGrammar bot 
    (Seq 
      (MkGrammar bot (Seq (plus digit) (charSet "."))) (plus digit) )))

export
delim : {ct : Vect n Type} -> Grammar ct a -> Grammar ct b  -> Grammar ct c
        -> Grammar ct b
delim left p right = 
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

maybe : {ct : Vect n Type} -> Grammar ct a -> Grammar ct (Maybe a)
maybe p = any [
  MkGrammar bot (Map (\x => Just x) p),
  MkGrammar bot (Eps Nothing)
]

export
com : {a : Type} -> {n : Nat} -> {ct : Vect n Type} -> Grammar ct a -> 
        Grammar ct (List a)
com g = 
  MkGrammar bot (Fix {a = List a} (com' g))
  where
    com' : Grammar ct a -> Grammar (List a :: ct) (List a)
    com' g = 
      MkGrammar bot (Alt 
                      (MkGrammar bot (Eps []))
                      (MkGrammar bot 
                        (Map (\(x, xs) => case xs of 
                                               Nothing => [x]
                                               Just(_, rest) => x :: rest) 
                          (MkGrammar bot 
                            (Seq 
                              (wekeanGrammar g)
                              (maybe (MkGrammar bot (Seq comma (MkGrammar bot (Var Z)))))
                            )))))


map' : List (JsonToken Double) -> List JsonValue
map' [] = []
map' ((TDecimal dbl) :: xs) = JDecimal dbl :: map' xs


value :  Grammar Nil JsonValue
value = MkGrammar bot (Fix {a = JsonValue} value')
  where
    value' : Grammar [JsonValue] JsonValue
    value' = 
      let arr = MkGrammar bot (Map (\arf => JArray arf) (delim lbracket (com (MkGrammar bot (Var Z))) rbracket))
          decmap = MkGrammar bot (Map (\(TDecimal db) => JDecimal db ) decimal)
          stringmap = MkGrammar bot (Map (\(TString s) => JString s ) stringp)
          nullmap = MkGrammar bot (Map (\_ => JNull ) nullp)
          truemap = MkGrammar bot (Map (\_ => JBool True ) truep)
          falsemap = MkGrammar bot (Map (\_ => JBool False ) falsep) in 
        any [arr, decmap, stringmap, nullmap, truemap, falsemap]