module Parser 

import Grammar
import Data.SortedSet
import Data.List
import Data.Ref


record Parser a where 
  constructor MkParser 
  gt : Either String GT
  parse : List Char -> Either String (a , List Char)


export
parse' : Parser a -> List Char -> Either String (a , List Char)
parse' (MkParser gt p) cs = p cs



matchChar : Char -> List Char -> Either String (Char , List Char)
matchChar c [] = Left "No more characters to parse"
matchChar c cs@(x :: xs) = if x == c then Right (x, xs) else Left "Parser failed"

export
chr : Char -> Parser Char
chr c = 
  MkParser
    { gt = Right (char c)
    , parse  = matchChar c
    }
    

-- epsParser : List Char -> (Maybe () , List Char)
-- epsParser [] = (Just (), [])
-- epsParser (x :: xs) = ?feps

export
eps : Parser ()
eps = 
  MkParser
    { gt = Right eps
    , parse  = (\cs => Right ((), cs))
    }
    

export
bot : Parser a
bot = 
  MkParser
    { gt =  Right bot
    , parse  = (\cs => Left "Failed parser")
    }

export
seq : Parser a -> Parser b -> Parser (a, b)
seq (MkParser gt1 parse1) (MkParser gt2 parse2) =
  MkParser
    {
      gt = do 
              g1 <- gt1 
              g2 <- gt2 
              seq g1 g2
    , parse = (\cs => 
                    do 
                        (a, rest) <- parse1 cs 
                        (b, rest) <- parse2 rest
                        Right ((a, b), rest))
    }

alt_parse : (List Char -> Either String (a, List Char)) 
      -> (List Char -> Either String (a, List Char))
      -> List Char -> Char -> GT -> GT -> Either String (a, List Char)
alt_parse f g cs c x y = 
  if contains c x.first then 
    f cs
  else if contains c y.first then
    g cs
  else if x.null then
    f cs 
  else if y.null then
    g cs 
  else 
    Left "Parser failed!!"                

export
alt : Parser a -> Parser a -> Parser a
alt (MkParser gt1 parse1) (MkParser gt2 parse2) =
  MkParser 
    {
      gt = do 
              g1 <- gt1 
              g2 <- gt2 
              alt g1 g2
    , parse = (\cs => 
                  case head' cs of 
                    Just hd => do 
                                  g1 <- gt1 
                                  g2 <- gt2 
                                  alt_parse parse1 parse2 cs hd g1 g2

                    Nothing => Left "Nothing to parse!")
    }



export
map : (a -> b) -> Parser a -> Parser b
map f (MkParser gt parse) = 
  MkParser 
    {
      gt = gt
    , parse = (\cs => 
                  do 
                    (a, rest) <- parse cs
                    Right (f a, rest))
    }

fix' : ((a -> a) -> a -> a) -> a -> a
fix' f x = f (fix' f) x

export
fix'' : ((Parser a -> Parser a) -> Parser a -> Parser a) -> Parser a -> Parser a
fix'' f x = ?lll

export
fix : (Parser a -> Parser a) -> Parser a
fix f =
  let h : Parser a
      h = f (MkParser
          {
            -- update to correct grammar
            gt = Right (char 'a')
          , parse = (\cs => h.parse cs)
          })
  in h

export
any : List (Parser a) -> Parser a 
any xs = foldl alt bot xs


charset : String -> Parser Char
charset str = any (map chr (unpack str))

always : a -> a -> a
always x = \_ => x

star : Parser a -> Parser (List a)
star x = fix (\f => alt (map (\y => []) eps) (map (\(c, cs) => c :: cs) (seq x f)))
-- star = 
--   fix (\f => \x =>
--     MkPT 
--       {
--         gt = ?gt_fix
--       , parse = ?llkkk
--       })
-- star = fix (\f => \x => 
--           alt (map (\y => []) eps) (map (\l => fst l :: snd l) (seq x (f x))))


-- fix_lazy : Lazy((Parser a  -> Parser b) -> Parser a  -> Parser b) 
--           -> Parser a -> Parser b
-- fix_lazy f = f (fix_lazy (Delay f))


-- star_lazy : Parser a -> Parser (List a)
-- star_lazy = fix_lazy (\f => \x => 
--               any   
--               [ map (\y => []) eps
--               , map (\l => fst l :: snd l) (seq x (f x))
--               ]
--             )

-- -- star_lazy : Parser a -> Parser (List a)
-- -- star_lazy = fix_lazy (\f => \x => 
-- --               any   
-- --               [ 
-- --                 map (\y => [y]) x
-- --               ]
-- --             )

