module Language

import Data.SortedSet

public export
record LangType (tok : Type) where 
  constructor MkLangType
  null : Bool
  first : SortedSet tok
  follow : SortedSet tok
  guarded : Bool

export
Eq tok => Eq (LangType tok) where 
  t1 == t2 = 
    t1.null == t2.null && t1.first == t2.first && t1.follow == t2.follow

export
Show tok => Show (LangType tok) where 
  show (MkLangType null first follow guarded) = 
    """
    { null : \{show null}
    , first : \{show first}
    , follow : \{show follow}
    , guarded : \{show guarded}
    } 
    """

export
char : Ord tok => tok -> LangType tok
char c = 
  MkLangType
    { null  = False
    , first = singleton c
    , follow = empty 
    , guarded = True
    }

export
eps : Ord tok => LangType tok
eps =
  MkLangType
    { null  = True
    , first = empty
    , follow = empty 
    , guarded = True
    }

export 
bot : Ord tok => LangType tok
bot = 
  MkLangType
    { null  = False
    , first = empty
    , follow = empty 
    , guarded = True
    }


export
apart : Ord tok => LangType tok -> LangType tok -> Bool
apart t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)


export
seq : Show tok => Ord tok => LangType tok -> LangType tok -> Either String (LangType tok)
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
disjoint : Ord tok => LangType tok -> LangType tok -> Bool
disjoint t1 t2 = 
  not (t1.null && t2.null) && (intersection t1.first t2.first == empty)


export 
alt : Show tok => Ord tok => LangType tok -> LangType tok -> 
      Either String (LangType tok)
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

min : Ord tok => LangType tok
min = 
  MkLangType
    { null  = False
    , first = empty
    , follow = empty 
    , guarded = False
    }

export
fix : Ord tok => (Either String (LangType tok) -> Either String (LangType tok)) 
      -> Either String (LangType tok) 
fix f = fixHelper $ Right min

  where
    fixHelper : Either String (LangType tok) -> Either String (LangType tok) 
    fixHelper t = 
      let t' = f t in 
      if t' == t then t else fixHelper t'
