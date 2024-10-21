module Env
import Language


export
data Var : ctx -> a -> Type where 
    Z : Var (a , ctx) a
    S : Var rest a -> Var (a, rest) a

export
data Env : ctx -> Type where 
    Nil : Env ()
    (::) : LangType -> Env ctx -> Env (LangType, ctx)

export
lookup : Env ctx -> Var ctx a -> LangType
lookup (x :: _) Z = x
lookup (_ :: xs) (S n) = lookup xs n

export
map : (LangType -> LangType) -> Env ctx -> Env ctx
map f [] = []
map f (x :: xs) = f x :: map f xs
