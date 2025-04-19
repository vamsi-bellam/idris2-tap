module Env 

import Data.Vect

public export
data Var : (a : Type) -> (ctx : Vect n Type) -> Type where 
  Z : Var a (a :: rest)
  S : Var a rest -> Var a (b :: rest)

public export
Show (Var a ctx) where 
  show Z = "Z"
  show (S x) = "S " ++ show x