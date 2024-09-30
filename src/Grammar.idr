module Grammar

import Data.SortedSet

public export
record GT where 
  constructor MkGT
  null : Bool
  first : SortedSet Char
  follow : SortedSet Char

Eq GT where 
  t1 == t2 = 
    t1.null == t2.null && t1.first == t2.first && t1.follow == t2.follow

export
char : Char -> GT
char c = 
  MkGT
    { null  = False
    , first = insert c empty 
    , follow = empty 
    }

export
eps : GT 
eps =
  MkGT
    { null  = True
    , first = empty
    , follow = empty 
    }

export 
bot : GT 
bot = 
  MkGT
    { null  = False
    , first = empty
    , follow = empty 
    }


export
separate : GT -> GT -> Bool
separate t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)


export
seq : GT -> GT -> Either String GT
seq t1 t2 = 
  if separate t1 t2 then 
    Right(
      MkGT
        { null  = t1.null && t2.null
        , first = if t1.null then union t1.first t2.first else t1.first
        , follow = 
            if t2.null then union t2.follow (union t2.first t1.follow)
            else t2.follow         
        }
    )
  else Left "Given grammar is not separate"

export
nonOverlapping : GT -> GT -> Bool
nonOverlapping t1 t2 = 
  not (t1.null && t2.null) && (intersection t1.first t2.first == empty)


export 
alt : GT -> GT -> Either String GT
alt t1 t2 = 
  if nonOverlapping t1 t2 then 
    Right(
      MkGT
        { null  = t1.null || t2.null
        , first = union t1.first t2.first
        , follow = union t1.follow t2.follow   
        }
    )
  else 
    Left "Given grammar is overlapping"


export
fix : (GT -> GT) -> GT 
fix f = fixHelper bot 

  where
    fixHelper : GT -> GT 
    fixHelper t = 
      let t' = f t in 
      if t' == t then t else fixHelper t'
