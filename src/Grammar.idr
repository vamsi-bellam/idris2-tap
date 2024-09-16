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


separate : GT -> GT -> Bool
separate t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)

export
seq : GT -> GT -> Maybe GT
seq t1 t2 = 
  if separate t1 t2 then 
    Just(
      MkGT
        { null  = t1.null && t2.null
        , first = if t1.null then union t1.first t2.first else t1.first
        , follow = 
            if t2.null then union t2.follow (union t2.first t1.follow)
            else t2.follow         
        }
    )
  else Nothing

nonOverlapping : GT -> GT -> Bool
nonOverlapping t1 t2 = 
  not (t1.null && t2.null) && (intersection t1.first t2.first == empty)


export 
alt : GT -> GT -> Maybe GT
alt t1 t2 = 
  if nonOverlapping t1 t2 then 
    Just(
      MkGT
        { null  = t1.null || t2.null
        , first = union t1.first t2.first
        , follow = union t1.follow t2.follow   
        }
    )
  else Nothing


export
fix : (GT -> GT) -> GT 
fix f = fix_helper bot 

  where
    fix_helper : GT -> GT 
    fix_helper t = 
      let t' = f t in 
      if t' == t then t else fix_helper t'
