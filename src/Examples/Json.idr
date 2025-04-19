module Examples.Json

import Data.Vect
import Data.String

import Grammar
import Env
import Parser
import Examples.Utils
import Token

data JsonToken : Type -> Type where
  TNull : JsonToken ()
  TTrue : JsonToken Bool
  TFalse : JsonToken Bool
  TDecimal : JsonToken Double
  TString : JsonToken String
  TLBrace : JsonToken ()
  TRBrace : JsonToken ()
  TLBracket : JsonToken ()
  TRBracket : JsonToken ()
  TColon : JsonToken ()
  TComma : JsonToken ()

toInt : JsonToken a -> Int
toInt TNull = 0
toInt TTrue = 1
toInt TFalse = 2
toInt TDecimal = 3
toInt TString = 4
toInt TLBrace = 5
toInt TRBrace = 6
toInt TLBracket = 7
toInt TRBracket = 8
toInt TColon = 9
toInt TComma = 10

-- TNull < TTrue < TFalse < TDecimal < TString < TLBrace < TRBrace
-- < TLBracket < TRBracket < TColon < TComma
Tag JsonToken where
  compare TNull TNull = Eql
  compare TNull _ = Leq
  compare _ TNull = Geq

  compare TTrue TTrue = Eql
  compare TTrue _ = Leq
  compare _ TTrue = Geq

  compare TFalse TFalse = Eql
  compare TFalse _ = Leq
  compare _ TFalse = Geq

  compare TDecimal TDecimal = Eql
  compare TDecimal _ = Leq
  compare _ TDecimal = Geq

  compare TString TString = Eql
  compare TString _ = Leq
  compare _ TString = Geq

  compare TLBrace TLBrace = Eql
  compare TLBrace _ = Leq
  compare _ TLBrace = Geq

  compare TRBrace TRBrace = Eql
  compare TRBrace _ = Leq
  compare _ TRBrace = Geq

  compare TLBracket TLBracket = Eql
  compare TLBracket _ = Leq
  compare _ TLBracket = Geq

  compare TRBracket TRBracket = Eql
  compare TRBracket _ = Leq
  compare _ TRBracket = Geq

  compare TColon TColon = Eql
  compare TColon _ = Leq
  compare _ TColon = Geq

  compare TComma TComma = Eql
  compare TComma _ = Leq
  compare _ TComma = Geq


  show TNull = "TNull"
  show TTrue = "TTrue"
  show TFalse = "TFalse"
  show TDecimal = "TDecimal"
  show TString = "TString"
  show TLBrace = "TLBrace"
  show TRBrace = "TRBrace"
  show TLBracket = "TLBracket"
  show TRBracket = "TRBracket"
  show TColon = "TColon"
  show TComma = "TComma"

export
lbracket : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
lbracket = MkGrammar bot (Map (always (Tok TLBracket ())) (charSet "["))

export
rbracket : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
rbracket = MkGrammar bot (Map (always (Tok TRBracket ())) (charSet "]"))

export
lbrace : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
lbrace = MkGrammar bot (Map (always (Tok TLBrace ())) (charSet "{"))

export
rbrace : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
rbrace = MkGrammar bot (Map (always (Tok TRBrace ())) (charSet "}"))

export
comma : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
comma =  MkGrammar bot (Map (always (Tok TComma ())) (charSet ","))

export
colon : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
colon =  MkGrammar bot (Map (always (Tok TColon ())) (charSet ":"))


export
nullp : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
nullp = 
  MkGrammar bot 
  (Map (always (Tok TNull ())) 
    (MkGrammar bot 
      (Seq 
        (charSet "n") 
        (MkGrammar bot 
          (Seq (charSet "u") 
            (MkGrammar bot (Seq (charSet "l") (charSet "l"))))))))

export
truep : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
truep = 
  MkGrammar bot 
  (Map (always (Tok TTrue True)) 
    (MkGrammar bot 
      (Seq 
        (charSet "t") 
        (MkGrammar bot 
          (Seq (charSet "r") 
            (MkGrammar bot (Seq (charSet "u") (charSet "e"))))))))

export
falsep : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
falsep = 
  MkGrammar bot 
  (Map (always (Tok TFalse False)) 
    (MkGrammar bot 
      (Seq 
        (charSet "f") 
        (MkGrammar bot 
          (Seq (charSet "a") 
            (MkGrammar bot 
              (Seq (charSet "l") 
                (MkGrammar bot (Seq (charSet "s") (charSet "e"))))))))))

export
fullstringp : {n : Nat} -> {ct : Vect n Type} -> 
              Grammar ct (Token JsonToken) CharTag
fullstringp = 
  MkGrammar bot
  (Map (\((_, s), _) => Tok TString (pack s)) 
   (MkGrammar bot 
    (Seq 
      (MkGrammar bot (Seq (charSet "\"") (star (compCharSet "\"")))) 
      (charSet "\"") )))

export
decimal : {n : Nat} 
       -> {ct : Vect n Type} 
       -> Grammar ct (Token JsonToken) CharTag
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
    toDecimal : (List Char, Maybe (Char, List Char)) -> Token JsonToken
    toDecimal (num, Nothing) = Tok TDecimal (cast $ pack num)
    toDecimal (num, (Just (dot, frac))) = 
      Tok TDecimal (cast $ pack (num ++ [dot] ++ frac))
    

export
jsonToken : Grammar Nil (Token JsonToken) CharTag
jsonToken = 
  MkGrammar bot (Fix {a = Token JsonToken} jsonToken')
  where
    jsonToken' : Grammar [Token JsonToken] (Token JsonToken) CharTag
    jsonToken' = 
      any 
        [ lbracket
        , rbracket
        , lbrace
        , rbrace
        , comma
        , colon
        , nullp
        , truep
        , falsep
        , fullstringp
        , decimal
        , skipSpace (MkGrammar bot (Var Z))
        ]

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
sepByComma : {a : Type} 
          -> {n : Nat} 
          -> {ct : Vect n Type} 
          -> Grammar ct a JsonToken 
          -> Grammar ct (List a) JsonToken
sepByComma g = 
  MkGrammar bot (Fix {a = List a} (sepByComma' g))
  where
    sepByComma' : Grammar ct a JsonToken -> 
                  Grammar (List a :: ct) (List a) JsonToken
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
                            (Seq (tok TComma) (MkGrammar bot (Var Z))))))))))


                          
member : {a : Type} 
      -> {n : Nat} 
      -> {ct : Vect n Type} 
      -> Grammar ct a JsonToken 
      -> Grammar ct (String, a) JsonToken
member x = 
  MkGrammar 
    bot 
    (Map 
      (\((key, _), val) => (key, val)) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq (tok TString)  (tok TColon))) x)))

json : Grammar Nil JsonValue JsonToken
json = MkGrammar bot (Fix {a = JsonValue} json')
  where
    json' : Grammar [JsonValue] JsonValue JsonToken
    json' = 
      let object = 
            MkGrammar 
              bot 
              (Map 
                (\kvpairs => JObject kvpairs) 
                (between 
                  (tok TLBrace) 
                  (sepByComma (member (MkGrammar bot (Var Z)))) 
                  (tok TRBrace)))
          array = 
            MkGrammar 
              bot 
              (Map (\rest => JArray rest) 
                (between 
                  (tok TLBracket) 
                  (sepByComma (MkGrammar bot (Var Z))) 
                  (tok TRBracket)))
          decimal = MkGrammar bot (Map (\ db => JDecimal db ) (tok TDecimal))
          string = MkGrammar bot (Map (\s => JString s ) (tok TString) )
          null = MkGrammar bot (Map (always JNull) (tok TNull))
          true = MkGrammar bot (Map (always (JBool True)) (tok TTrue))
          false = MkGrammar bot (Map (always (JBool False)) (tok TFalse)) in 
      any [object, array, decimal, string, null, true, false]


export 
parseJSON : String -> Either String JsonValue
parseJSON input = do 
  lexedTokens <- lexer jsonToken (trim input)
  parser json lexedTokens