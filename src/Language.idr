module Language

import Data.SortedSet

public export
record LangType where 
  constructor MkLangType
  null : Bool
  first : SortedSet Char
  follow : SortedSet Char
  guarded : Bool

export
Eq LangType where 
  t1 == t2 = 
    t1.null == t2.null && t1.first == t2.first && t1.follow == t2.follow

export
Show LangType where 
  show (MkLangType null first follow guarded) = 
    """
    { null : \{show null}
    , first : \{show first}
    , follow : \{show follow}
    , guarded : \{show guarded}
    }
    
    """

export
char : Char -> LangType
char c = 
  MkLangType
    { null  = False
    , first = singleton c
    , follow = empty 
    , guarded = True
    }

export
eps : LangType 
eps =
  MkLangType
    { null  = True
    , first = empty
    , follow = empty 
    , guarded = True
    }

export 
bot : LangType 
bot = 
  MkLangType
    { null  = False
    , first = empty
    , follow = empty 
    , guarded = True
    }


export
apart : LangType -> LangType -> Bool
apart t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)


export
seq : LangType -> LangType -> Either String LangType
seq t1 t2 = 
  if apart t1 t2 then 
    Right(
      MkLangType
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
disjoint : LangType -> LangType -> Bool
disjoint t1 t2 = 
  not (t1.null && t2.null) && (intersection t1.first t2.first == empty)


export 
alt : LangType -> LangType -> Either String LangType
alt t1 t2 = 
  if disjoint t1 t2 then 
    Right(
      MkLangType
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
star :  LangType -> Either String LangType
star t = do 
            gt <- (seq t t)
            Right({null := True, follow := union t.first t.follow } gt)



export
fix : (Either String LangType -> Either String LangType) -> Either String LangType 
fix f = fixHelper (Right ({guarded := False} bot)) 

  where
    fixHelper : Either String LangType -> Either String LangType 
    fixHelper t = 
      let t' = f t in 
      if t' == t then t else fixHelper t'
