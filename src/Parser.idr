module Parser 

import Grammar
import Data.SortedSet
import Data.List

-- mkParserType : Type -> Type 
-- mkParserType a = List Char -> Either String (a , List Char)

record Parser a where 
  constructor MkParser 
  gt : Either String GT
  parse : List Char -> Either String (a , List Char)


export
applyParser : Parser a -> List Char -> Either String (a , List Char)
applyParser (MkParser gt p) cs = p cs

export
chr : Char -> Parser Char
chr c = 
  MkParser
    { gt = Right (char c)
    , parse  = matchChar c
    }
  
  where 
    matchChar : Char -> List Char -> Either String (Char , List Char)
    matchChar c [] = Left "Parser failed"
    matchChar c (x :: xs) = 
      if x == c then Right (x, xs) else Left "Parser failed!"
    
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
    , parse  = (\cs => Left "Parser failed")
    }

export
seq : Parser a -> Parser b -> Parser (a, b)
seq (MkParser gt1 parser1) (MkParser gt2 parser2) =
  MkParser
    {
      gt = do 
              g1 <- gt1 
              g2 <- gt2 
              seq g1 g2
    , parse = (\cs => 
                    do 
                        (a, rest) <- parser1 cs 
                        (b, rest) <- parser2 rest
                        Right ((a, b), rest))
    }

export
alt : Parser a -> Parser a -> Parser a
alt (MkParser gt1 parser1) (MkParser gt2 parser2) =
  MkParser 
    {
      gt = do 
              g1 <- gt1 
              g2 <- gt2 
              alt g1 g2
    , parse = (\cs => do 
                          g1 <- gt1 
                          g2 <- gt2 
                          case head' cs of 
                            Just hd => altParse parser1 parser2 cs hd g1 g2
                            Nothing => altParse2 parser1 parser2 cs g1 g2)
    }

  where 
    altParse : (List Char -> Either String (a, List Char)) 
              -> (List Char -> Either String (a, List Char))
              -> List Char -> Char -> GT -> GT -> Either String (a, List Char)
    altParse f g cs c x y = 
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

    altParse2 : (List Char -> Either String (a, List Char)) 
                -> (List Char -> Either String (a, List Char))
                -> List Char -> GT -> GT -> Either String (a, List Char)
    altParse2 f g cs x y = 
      if x.null then 
        f cs 
      else if y.null then 
        g cs
      else 
        Left "Parser failed!!"

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

export
fix : (Parser a -> Parser a) -> Parser a
fix f =
  let g : Either String GT  -> Either String GT
      g t = (f ({gt := t} bot)).gt in 
  let appliedParser : Parser a
      appliedParser = f (MkParser
          {
            gt = (Grammar.fix g)
          , parse = (\cs => appliedParser.parse cs)
          })
  in appliedParser

export
any : List (Parser a) -> Parser a 
any xs = foldl alt bot xs

charset : String -> Parser Char
charset str = any (map chr (unpack str))

always : a -> b -> a
always x = \_ => x

star : Parser a -> Parser (List a)
star x = 
  fix (\f => 
        any 
          [ map (always []) eps
          , map (\(c, cs) => c :: cs) (seq x f)
          ] 
      )


-- Examples

lower : Parser Char 
lower = charset "abcdefghijklmnopqrstuvwxyz"

upper : Parser Char 
upper = charset "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

word : Parser (List Char)
word = map (\(c, cs) => c :: cs) (seq upper (star lower))

data Token = SYMBOL (List Char) | LPAREN | RPAREN

symbol : Parser Token
symbol = map (\s => SYMBOL s) word

lparen : Parser Token
lparen = map (always LPAREN) (chr '(')

rparen : Parser Token
rparen = map (always RPAREN) (chr ')')

token : Parser Token
token = any [symbol, lparen, rparen]

data Sexp = Sym | Seq (List Sexp)

paren : Parser a -> Parser a
paren p = map (\(_, (a, _)) => a) (seq lparen (seq p rparen))

sexp : Parser Sexp
sexp = fix (\f => 
            any 
              [
                map (always Sym) symbol
              , map (\s => Seq s) (paren (star f))
              ])