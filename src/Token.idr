module Token 

public export
data Cmp : Type -> Type -> Type where
  Leq : Cmp a b          
  Eql : Cmp a a         
  Geq : Cmp a b        

public export
interface Tag (tagType : Type -> Type) where
  compare : tagType a -> tagType b -> Cmp a b
  show   : tagType a -> String   

public export
data Token : (tagType : Type -> Type) -> Type where
  Tok : {a : Type} -> (tag : tagType a) -> a -> Token tagType

public export
data TokenType : (tagType : Type -> Type) -> Type where
  TokType : {a : Type} -> (tag : tagType a) -> TokenType tagType

public export
{tagType : Type -> Type} -> Tag tagType => Eq (TokenType tagType) where
  TokType tag1 == TokType tag2 = 
    case (compare tag1 tag2) of 
      Leq => False
      Eql => True
      Geq => False

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

public export
{tagType : Type -> Type} -> Tag tagType => Show (Token tagType) where
  show (Tok tag y) = show tag

public export
{tagType : Type -> Type} -> Tag tagType => Show (TokenType tagType) where
  show (TokType tag) = show tag
