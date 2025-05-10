module Var 

import Data.Vect


||| Type-safe variable reference into a context vector.
||| Variables are represented in de Bruijn fashion.
|||
||| @a    The type of the variable being referred to.
||| @ctx  The context vector of available types.
public export
data Var : (a : Type) -> (ctx : Vect n Type) -> Type where 
  Z : Var a (a :: rest)
  S : Var a rest -> Var a (b :: rest)

export
Show (Var a ctx) where 
  show Z = "Z"
  show (S x) = "S " ++ show x
  