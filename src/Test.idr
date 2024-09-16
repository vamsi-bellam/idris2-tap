
fix : ((a -> b) -> a -> b) -> a -> b
fix f x = f (fix f) x

fact : Nat -> Nat
fact = fix (\recFact => \n => case n of
    0 => 1
    S k => n * recFact k)