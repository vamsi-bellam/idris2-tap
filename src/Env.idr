module Env
import Tp


export
data Var : ctx -> a -> Type where 
    Z : Var (a , ctx) a
    S : Var rest a -> Var (a, rest) a

export
data Env : ctx -> Type where 
    Nil : Env ()
    (::) : Tp.TP -> Env ctx -> Env (Tp.TP, ctx)

export
lookup : Env ctx -> Var ctx a -> Tp.TP
lookup (x :: _) Z = x
lookup (_ :: xs) (S n) = lookup xs n

export
map : (Tp.TP -> Tp.TP) -> Env ctx -> Env ctx
map f [] = []
map f (x :: xs) = f x :: map f xs
