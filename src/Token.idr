module Token 


||| A type-level result of comparing two values indexed by types `a` and `b`.
|||
||| @a The type index of the first value.
||| @b The type index of the second value.
public export
data Cmp : Type -> Type -> Type where
  Leq : Cmp a b          
  Eql : Cmp a a         
  Geq : Cmp a b        


||| Interface for comparing and showing tag values.
||| A tag is a value of type `tagType a`, parameterized by its type index `a`.
|||
||| Implementations must:
||| - Provide a total ordering via `compare`.
||| - Render tags as human-readable strings via `show`.
|||
||| @tagType A type-indexed tag constructor.
|||
||| Example - A type constructor `IntOrStr` with two constructors(also called tags)
||| data IntOrStr : Type -> Type where 
|||   In : IntOrStr Int
|||   St : IntOrStr String 

||| Tag IntOrStr where
|||   compare In In = Eql
|||   compare St St = Eql
|||   compare In St = Leq
|||   compare St In = Geq
  
|||   show In = "In"
|||   show St = "St"
public export
interface Tag (tagType : Type -> Type) where
  compare : tagType a -> tagType b -> Cmp a b
  show   : tagType a -> String   


||| A typed token that pairs a tag with its corresponding value.
||| The type `a` ensures the value matches what the tag expects.
|||
||| @tagType A type-indexed tag constructor.
||| @a       The type of the value associated with the tag.
public export
data Token : (tagType : Type -> Type) -> Type where
  Tok : {a : Type} -> (tag : tagType a) -> a -> Token tagType

||| A type-erased version of `Token` that holds only the tag.
|||
||| @tagType A type-indexed tag constructor.
||| @a       The type of the value associated with the tag.
public export
data TokenType : (tagType : Type -> Type) -> Type where
  TokType : {a : Type} -> (tag : tagType a) -> TokenType tagType


||| Implenents `Eq` interface for `TokenType tagType` and uses the `compare`
||| from `Tag` interface. 
public export
{tagType : Type -> Type} -> Tag tagType => Eq (TokenType tagType) where
  TokType tag1 == TokType tag2 = 
    case (compare tag1 tag2) of 
      Leq => False
      Eql => True
      Geq => False

||| Implenents `Ord` interface for `TokenType tagType` and uses the `compare`
||| from `Tag` interface. 
public export
{tagType : Type -> Type} 
-> Tag tagType 
=> Eq (TokenType tagType) 
=> Ord (TokenType tagType) where
  compare (TokType tag1) (TokType tag2) = 
    case compare tag1 tag2 of 
      Leq => LT
      Eql => EQ
      Geq => GT

||| Implenents `Show` interface for `Token tagType` and uses the `show`
||| from `Tag` interface. 
public export
{tagType : Type -> Type} -> Tag tagType => Show (Token tagType) where
  show (Tok tag y) = show tag

||| Implenents `Show` interface for `TokenType tagType` and uses the `show`
||| from `Tag` interface. 
public export
{tagType : Type -> Type} -> Tag tagType => Show (TokenType tagType) where
  show (TokType tag) = show tag
