module Grammar

import Data.SortedSet

public export
record GT where 
  constructor MkGT
  null : Bool
  first : SortedSet Char
  follow : SortedSet Char

export
Eq GT where 
  t1 == t2 = 
    t1.null == t2.null && t1.first == t2.first && t1.follow == t2.follow

export
Show GT where 
  show (MkGT null first follow) = 
    """
    { null : \{show null}
    , first : \{show first}
    , follow : \{show follow}
    """

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
apart : GT -> GT -> Bool
apart t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)


export
seq : GT -> GT -> Either String GT
seq t1 t2 = 
  if apart t1 t2 then 
    Right(
      MkGT
        { null = False
          -- null  = t1.null && t2.null
        , first = t1.first
          -- first = if t1.null then union t1.first t2.first else t1.first
        , follow = 
            if t2.null then union t2.follow (union t2.first t1.follow)
            else t2.follow         
        }
    )
  else Left "Concatenated languages can't be uniquely broken!"

export
disjoint : GT -> GT -> Bool
disjoint t1 t2 = 
  not (t1.null && t2.null) && (intersection t1.first t2.first == empty)


export 
alt : GT -> GT -> Either String GT
alt t1 t2 = 
  if disjoint t1 t2 then 
    Right(
      MkGT
        { null  = t1.null || t2.null
        , first = union t1.first t2.first
        , follow = union t1.follow t2.follow   
        }
    )
  else 
    Left "Languages are not disjoint!"


export
fix : (Either String GT -> Either String GT) -> Either String GT 
fix f = fixHelper (Right bot) 

  where
    fixHelper : Either String GT -> Either String GT 
    fixHelper t = 
      let t' = f t in 
      if t' == t then t else fixHelper t'
