-- module Hoas

-- import Grammar
-- import Data.Vect
-- import Parser
-- import Env
-- import Debug.Trace
-- import Decidable.Equality


-- public export
-- data Ctx : Vect n Type -> Type where
--   Nil  : Ctx []
--   (::) : (a : Type) -> Ctx as -> Ctx (a :: as)

-- len : Ctx ct  -> Nat
-- len [] = 0
-- len (x :: y) = S (len y)

-- HT : Type -> Type
-- HT a = {n : Nat} -> {ct : Vect n Type} -> Ctx ct -> Grammar ct a 

-- Show (HT a) where 
--   show _ = "<abstract>"

-- eps : HT ()
-- eps _ = MkGrammar bot (Eps ())

-- char : Char -> HT Char
-- char c _ = MkGrammar bot (Tok c)

-- seq : HT a -> HT b -> HT (a, b)
-- seq f g ctx = MkGrammar bot (Seq (f ctx) (g ctx))

-- bot : HT a
-- bot _ = MkGrammar bot Bot

-- alt : HT a -> HT a -> HT a
-- alt f g ctx = MkGrammar bot (Alt (f ctx) (g ctx))


-- tshift : {a : Type} -> {ct1 : Vect n Type} -> {ct2 : Vect m Type} ->
--           Nat -> (ctx1 : Ctx ct1) -> (ctx2 : Ctx (a :: ct2)) -> Var a ct1
-- tshift Z (x :: xs) (y :: ys) = ?ff
-- tshift (S k) (x :: xs) (ys)  = S (tshift k xs ys)
-- tshift _ _ _ = believe_me ()

-- data Extends : Ctx ct1 -> Ctx ct2 -> Type where
--   Same  : Extends ctx ctx              
--   Extend : Extends ctx1 ctx2 -> Extends (a :: ctx1) ctx2

-- tshift' : {a : Type} -> {ct1 : Vect n Type} -> {ct2 : Vect m Type} ->
--           (ctx1 : Ctx ct1) -> (ctx2 : Ctx (a :: ct2)) -> 
--           Extends ctx1 ctx2 -> Var a ct1
-- tshift' ctx ctx Same = Z
-- tshift' (x :: ctx1) ctx2 (Extend prf) = S (tshift' ctx1 ctx2 prf)

-- fix : {a : Type} -> (HT a -> HT a) -> HT a
-- fix f ctx = 
--   let ctx' = (a :: ctx) 
--       mkHT : HT a
--       mkHT ctx1 = 
--         MkGrammar 
--           bot 
--           (Var (tshift' ctx1 ctx' (believe_me {b = Extends ctx1 ctx'} ())))
--   in
--   MkGrammar bot (Fix ((f (mkHT)) ctx'))

-- -- testing examples
-- ctx' : Ctx [Int]
-- ctx' = Int :: Nil

-- ctx : Ctx [Bool, Int] 
-- ctx = Bool :: (Int :: Nil)

-- example : Var Int [Bool, Int]
-- example = tshift' ctx ctx' (Extend Same)

-- example1 : Var Int [Bool, Int]
-- example1 = tshift' ctx ctx' (believe_me {b = Extends ctx ctx'} ())


-- map : (a -> b) -> HT a -> HT b
-- map f g ctx = MkGrammar bot (Map f (g ctx))

-- any : List (HT a) -> HT a
-- any ls = foldl alt bot ls

-- always : a -> b -> a
-- always x = \_ => x

-- star : {a : Type} -> HT a -> HT (List a)
-- star g = 
--   fix (\rest => 
--         any 
--           [ map (always []) eps 
--           , map (\(c, cs) => c :: cs) (seq g rest) 
--           ] 
--       )

-- typeCheck : HT a -> Either String (Grammar Nil a)
-- typeCheck parser = typeof [] (parser Nil) 

-- genParser : HT a -> Either String (Parser a)
-- genParser parser = do 
--         typedGrammar <- typeCheck parser
--         Right (parse typedGrammar (Empty))


-- examples 

-- charset : String -> HT Char
-- charset str = any (map char (unpack str))

-- lower : HT Char 
-- lower = charset "abcdefghijklmnopqrstuvwxyz"

-- upper : HT Char 
-- upper = charset "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

-- word : HT (List Char)
-- word = map (\(c, cs) => c :: cs) (seq upper (star lower))

-- data Token = SYMBOL (List Char) | LPAREN | RPAREN

-- symbol : HT Token
-- symbol = map (\s => SYMBOL s) word

-- lparen : HT Token
-- lparen = map (always LPAREN) (char '(')

-- rparen : HT Token
-- rparen = map (always RPAREN) (char ')')

-- token : HT Token
-- token = any [symbol, lparen, rparen]

-- data Sexp = Sym | Seq (List Sexp)

-- paren : HT a -> HT a
-- paren p = map (\((_, a), _) => a) (seq (seq lparen p) rparen)

-- exParen : HT (List (Char, Char))
-- exParen = star (paren (seq (char 'a') (alt (char 'b') (char 'c')) ))

-- sexp : HT Sexp 
-- sexp = fix (\f => 
--             any 
--               [
--                 map (always Sym) symbol
--               , map (\s => Seq s) (paren (star f))
--               ])