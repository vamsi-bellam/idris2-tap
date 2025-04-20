module Language

import Data.SortedSet

public export
record LangType (token : Type) where 
  constructor MkLangType
  null : Bool
  first : SortedSet token
  follow : SortedSet token
  guarded : Bool

export
Eq token => Eq (LangType token) where 
  t1 == t2 = 
    t1.null == t2.null && t1.first == t2.first && t1.follow == t2.follow

export
Show token => Show (LangType token) where 
  show (MkLangType null first follow guarded) = 
    """
    { null : \{show null}
    , first : \{show first}
    , follow : \{show follow}
    , guarded : \{show guarded}
    } 
    """

export
tok : {auto _ : Ord token} -> token -> LangType token
tok c = 
  MkLangType
    { null  = False
    , first = singleton c
    , follow = empty 
    , guarded = True
    }

export
eps : {auto _ : Ord token} -> LangType token
eps =
  MkLangType
    { null  = True
    , first = empty
    , follow = empty 
    , guarded = True
    }

export 
bot : {auto _ : Ord token} -> LangType token
bot = 
  MkLangType
    { null  = False
    , first = empty
    , follow = empty 
    , guarded = True
    }

export
seq : {auto _ : Show token} 
   -> {auto _ : Ord token} 
   -> LangType token 
   -> LangType token 
   -> Either String (LangType token)
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
  
  where 
    apart : LangType token -> LangType token -> Bool
    apart t1 t2 = not (t1.null) && (intersection t1.follow t2.first == empty)

export 
alt : {auto _ : Show token} 
   -> {auto _ : Ord token} 
   -> LangType token 
   -> LangType token 
   -> Either String (LangType token)
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
  where 
    disjoint : LangType token -> LangType token -> Bool
    disjoint t1 t2 = 
      not (t1.null && t2.null) && (intersection t1.first t2.first == empty)

export
fix : {auto _ : Ord token} 
   -> (f : Either String (LangType token) -> Either String (LangType token)) 
   -> Either String (LangType token) 
fix f = fixHelper $ Right min

  where
    fixHelper : Either String (LangType token) -> Either String (LangType token) 
    fixHelper t = 
      let t' = f t in 
      if t' == t then t else fixHelper t'

    min : LangType token
    min = 
      MkLangType
        { null  = False
        , first = empty
        , follow = empty 
        , guarded = False
        }
