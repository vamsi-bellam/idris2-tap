module Env
import Language

public export
data Var : (ctx : Type) -> (a : Type) -> Type where
  Z : Var (a, rest) a
  S : Var rest a -> Var (b, rest) a

public export
data Env : (ctx : Type) -> Type where
  Nil  : Env ()
  (::) : a -> Env ctx -> Env (a, ctx)

public export
lookup : Env ctx -> Var ctx a -> a
lookup (x :: _)  Z = x
lookup (_ :: xs) (S n) = lookup xs n

public export
map : (f : forall a. a -> a) -> Env ctx -> Env ctx
map fn [] = []
map fn (x :: xs) = fn x :: map fn xs
