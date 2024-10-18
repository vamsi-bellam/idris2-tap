module Tp

import Data.SortedSet

public export
record TP where 
  constructor MkGT
  null : Bool
  first : SortedSet Char
  follow : SortedSet Char
  guarded : Bool

export
Eq TP where 
  t1 == t2 = 
    t1.null == t2.null && t1.first == t2.first && t1.follow == t2.follow

export
Show TP where 
  show (MkGT null first follow guarded) = 
    """
    { null : \{show null}
    , first : \{show first}
    , follow : \{show follow}
    , guarded : \{show guarded}
    }
    
    """

export
char : Char -> TP
char c = 
  MkGT
    { null  = False
    , first = singleton c
    , follow = empty 
    , guarded = True
    }

export
eps : TP 
eps =
  MkGT
    { null  = True
    , first = empty
    , follow = empty 
    , guarded = True
    }

export 
bot : TP 
bot = 
  MkGT
    { null  = False
    , first = empty
    , follow = empty 
    , guarded = True
    }


export
apart : TP -> TP -> Bool
apart t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)


export
seq : TP -> TP -> Either String TP
seq t1 t2 = 
  if apart t1 t2 then 
    Right(
      MkGT
        { 
          null  = t1.null && t2.null
        , first = if t1.null then union t1.first t2.first else t1.first
        , follow = 
            if t2.null then union t2.follow (union t2.first t1.follow)
            else t2.follow
        , guarded = t1.guarded      
        }
    )
  else Left ("""
              The Languages 
              \{show t1} 
              \{show t2}
              are not apart!
            """)

export
disjoint : TP -> TP -> Bool
disjoint t1 t2 = 
  not (t1.null && t2.null) && (intersection t1.first t2.first == empty)


export 
alt : TP -> TP -> Either String TP
alt t1 t2 = 
  if disjoint t1 t2 then 
    Right(
      MkGT
        { null  = t1.null || t2.null
        , first = union t1.first t2.first
        , follow = union t1.follow t2.follow  
        , guarded = t1.guarded && t2.guarded 
        } 
    )
  else 
    Left ("""
              The Languages 
              \{show t1} 
              \{show t2}
              are not disjoint!
          """)

export
star :  TP -> Either String TP
star t = do 
            gt <- (seq t t)
            Right({null := True, follow := union t.first t.follow } gt)



export
fix : (Either String TP -> Either String TP) -> Either String TP 
fix f = fixHelper (Right ({guarded := False} bot)) 

  where
    fixHelper : Either String TP -> Either String TP 
    fixHelper t = 
      let t' = f t in 
      if t' == t then t else fixHelper t'
