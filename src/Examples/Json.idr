module Examples.Json

import Data.Vect
import Data.String

import Grammar
import Var
import Parser
import Token

import Examples.Utils

%hide Prelude.Ops.infixr.(<|>)

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


lbracket : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
lbracket = char '[' $$ always (Tok TLBracket ()) 

rbracket : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
rbracket = char ']' $$ always (Tok TRBracket ()) 

lbrace : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
lbrace = char '{' $$ always (Tok TLBrace ())

rbrace : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
rbrace = char '}' $$ always (Tok TRBrace ())

comma : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
comma = char ',' $$ always (Tok TComma ()) 

colon : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
colon = char ':' $$ always (Tok TColon ())

nullp : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
nullp = (char 'n' >>> char 'u' >>> char 'l' >>> char 'l') $$ 
        always (Tok TNull ())

truep : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
truep = (char 't' >>> char 'r' >>> char 'u' >>> char 'e') $$ 
        always (Tok TTrue True)

falsep : {ct : Vect n Type} -> Grammar ct (Token JsonToken) CharTag
falsep = (char 'f' >>> char 'a' >>> char 'l' >>> char 's' >>> char 'e') $$ 
          always (Tok TFalse False)

fullstringp : {n : Nat} 
           -> {ct : Vect n Type} 
           -> Grammar ct (Token JsonToken) CharTag
fullstringp = (char '"' >>> star (compCharSet "\"") >>> char '"') $$ 
              (\((_, s), _) => Tok TString (pack s)) 

decimal : {n : Nat} 
       -> {ct : Vect n Type} 
       -> Grammar ct (Token JsonToken) CharTag
decimal = (plus digit >>> maybe (char '.' >>> plus digit)) $$ toDecimal
  where 
    toDecimal : (List Char, Maybe (Char, List Char)) -> Token JsonToken
    toDecimal (num, Nothing) = Tok TDecimal (cast $ pack num)
    toDecimal (num, (Just (dot, frac))) = 
      Tok TDecimal (cast $ pack (num ++ [dot] ++ frac))
    
jsonToken : Grammar Nil (Token JsonToken) CharTag
jsonToken = fix jsonToken'
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
        , skipSpace (var Z)
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


sepByComma : {a : Type} 
          -> {n : Nat} 
          -> {ct : Vect n Type} 
          -> Grammar ct a JsonToken 
          -> Grammar ct (List a) JsonToken
sepByComma g = fix (sepByComma' g)

  where
    sepByComma' : Grammar ct a JsonToken 
               -> Grammar (List a :: ct) (List a) JsonToken
    sepByComma' g =  
        eps [] <|> ((wekeanGrammar g >>> maybe (tok TComma >>> var Z)) $$ toList)

      where 
        toList : (a, Maybe ((), List a)) -> List a
        toList (x, Nothing) = [x]
        toList (x, (Just y)) = x :: (snd y)


                          
member : {a : Type} 
      -> {n : Nat} 
      -> {ct : Vect n Type} 
      -> Grammar ct a JsonToken 
      -> Grammar ct (String, a) JsonToken
member x = (tok TString >>> tok TColon >>> x) $$ (\((key, _), val) => (key, val))

json : Grammar Nil JsonValue JsonToken
json = fix json'
  where
    json' : Grammar [JsonValue] JsonValue JsonToken
    json' = 
      let object = (between 
                      (tok TLBrace) 
                      (sepByComma (member (var Z))) 
                      (tok TRBrace)) $$ 
                    JObject
          array = (between (tok TLBracket) (sepByComma (var Z)) (tok TRBracket)) 
                  $$ JArray
          decimal = tok TDecimal $$ JDecimal
          string = tok TString$$ JString
          null = tok TNull $$ always JNull 
          true = tok TTrue $$ always (JBool True) 
          false = tok TFalse $$ always (JBool False) in 
      any [object, array, decimal, string, null, true, false]

export
parseJSON : String -> Either String JsonValue
parseJSON input = do 
  lexedTokens <- lexer jsonToken (trim input)
  parser json lexedTokens