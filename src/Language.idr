module Language

import Data.SortedSet


||| LangType represents essential properties of a grammar construct used in 
||| parsing.
|||
||| @token   The type of tokens used in the grammar.
||| @null    True if the language described can produce the empty string.
||| @first   The set of tokens that can appear at the beginning of some string 
||| in the language.
||| @follow  The set of tokens which can follow the last character of a string 
||| in the language.
||| @guarded True if the type is guarded, used to track whether the type is in 
||| guarded context or not and helpful while type chekcing.

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

||| Builds `LangType` for the grammar that accepts only the given token.
export
tok : {auto _ : Ord token} -> token -> LangType token
tok c = 
  MkLangType
    { null  = False
    , first = singleton c
    , follow = empty 
    , guarded = True
    }

||| Builds `LangType` for the grammar that has just empty string.
export
eps : {auto _ : Ord token} -> LangType token
eps =
  MkLangType
    { null  = True
    , first = empty
    , follow = empty 
    , guarded = True
    }

||| Builds `LangType` for the grammar that is invalid.
export 
bot : {auto _ : Ord token} -> LangType token
bot = 
  MkLangType
    { null  = False
    , first = empty
    , follow = empty 
    , guarded = True
    }

||| Builds `LangType` for the sequential composition (concatenation) of two 
||| grammars with `LangType` values `L1` and `L2`.
||| However, for the composition to be valid, the two languages must be **apart**.
||| This means they are syntactically disjoint to prevent parsing ambiguity:
||| - `L1` must not be nullable.
||| - `L1.follow` and `L2.first` must be disjoint.
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

||| Builds `LangType` for the alternation (choice) of two grammars with 
||| `LangType` values `L1` and `L2`.
||| For the choice to be well-formed and unambiguous, the two branches must be 
||| **disjoint**:
||| - They must not both accept the empty string.
||| - Their `first` sets must be disjoint.
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

||| Builds the `LangType` for the recursive grammars.
||| Computes the least fixed point of a language transformer function `f`,
||| representing a recursive grammar definition.
||| The fixpoint iteration begins with the least language:
||| - Not nullable (`null = False`)
||| - Empty `first` and `follow` sets
||| - Not guarded (`guarded = False`)
||| The iteration proceeds until a fixed point is reached.
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
