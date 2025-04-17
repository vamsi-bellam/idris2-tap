module Token 


public export
data Cmp : Type -> Type -> Type where
  Leq : Cmp a b          
  Eql : Cmp a a         
  Geq : Cmp a b        

public export
interface Tag (t : Type -> Type) where
  compare : t a -> t b -> Cmp a b
  print   : t a -> String   

public export
data Token : (Type -> Type) -> Type where
  Tok : {a : Type} -> t a -> a -> Token t

public export
data TokenType : (t : Type -> Type) -> Type where
  TokType : {a : Type} -> t a -> TokenType t



public export
{t : Type -> Type} -> Tag t => Eq (TokenType t) where
  TokType x == TokType y = 
    case (compare x y) of 
      Leq => False
      Eql => True
      Geq => False


public export
{t : Type -> Type} -> Tag t => Eq (TokenType t) => Ord (TokenType t) where
  compare (TokType x) (TokType z) = 
    case compare x z of 
      Leq => LT
      Eql => EQ
      Geq => GT

public export
{t : Type -> Type} -> Tag t => Show (Token t) where
  show (Tok x y) = print x

public export
{t : Type -> Type} -> Tag t => Show (TokenType t) where
  show (TokType tag) = print tag
