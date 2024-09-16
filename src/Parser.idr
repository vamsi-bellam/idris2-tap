module Parser 

public export
data Parser : (a : Type) -> Type where 
    MkParser : (List Char -> (Maybe a, List Char)) -> Parser a

export
parse : Parser a -> List Char -> (Maybe a, List Char)
parse (MkParser f) cs = f cs



matchChar : Char -> List Char -> (Maybe Char, List Char)
matchChar c cs = 
  case cs of 
    [] => (Nothing, cs)
    (x :: xs) => if x == c then (Just x, xs) else (Nothing, cs)

export
chr : Char -> Parser Char
chr c = MkParser (matchChar c)

export
eps : Parser ()
eps = MkParser (\cs => (Just (), cs))

export
bot : Parser a
bot = MkParser (\cs => (Nothing, cs))

seq_helper : Parser a -> Parser b -> List Char -> (Maybe (a, b), List Char)
seq_helper x y cs = 
  case parse x cs of 
    (Nothing, cs) => (Nothing, cs)
    (Just x, xs) => case parse y xs of 
                      (Nothing, xs) => (Nothing, cs)
                      (Just y, ys) => (Just (x, y), ys)

export
seq : Parser a -> Parser b -> Parser (a ,  b)
seq x y = MkParser (seq_helper x y)

alt_helper : Parser a -> Parser a -> List Char -> (Maybe a, List Char)
alt_helper x y cs = 
  case (parse x cs) of 
    (Nothing, _) => parse y cs
    _ => parse x cs

export
alt : Parser a -> Parser a -> Parser a
alt x y = MkParser (alt_helper x y)



map_helper : Parser a -> (a -> b) -> List Char -> (Maybe b, List Char)
map_helper x f cs = 
  case parse x cs of
    (Nothing, z) => (Nothing, z)
    ((Just y), z) => (Just (f y), z)

export
map : (a -> b) -> Parser a -> Parser b
map f pa = MkParser (map_helper pa f)


Eq (Parser a) where
  (MkParser f) == (MkParser g) = ?llk

fix_helper : (Parser a -> Parser a) -> Parser a
fix_helper f = loop bot 

  where 
    loop : Parser a -> Parser a 
    loop t = if f t == t then f t else t 


export
fix : ((Parser a -> Parser b) -> Parser a -> Parser b) -> Parser a -> Parser b
fix f x = f (fix f) x

export
any : List (Parser a) -> Parser a 
any xs = foldl alt bot xs


charset : String -> Parser Char
charset str = any (map chr (unpack str))

always : a -> a -> a
always x = \_ => x

star : Parser a -> Parser (List a)
star g = fix (\f => \x => 
          any [map (\y => []) eps, map (\l => fst l :: snd l) (seq x (f x))]) g

