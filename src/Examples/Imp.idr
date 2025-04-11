module Examples.Imp

import Data.Vect

import Grammar
import Env
import Examples.Utils
import Parser

{- 

Arithmetic Expressions 

a ::= n | X | a0 + a1 | a0 - a1 | a0 * a1 

Boolean Expressions 

b ::= true | false | a0 = a1 | a0 <= a1 | !b | b0 && b1 | b0 || b1 | (b)

Commands 

c ::= skip | let X := a | c0;c1 | if b then c0 else c1 | while b do c | (c)

-}

keywords : Vect 9 String
keywords = ["if", "then", "else", "true", "false", "skip", "while", "do", "let"]

data Aop = APlus | AMinus | AMult
data Bop = BEq | BLte
data Bop2 = BAnd | Bor
data Id = ID

data IToken : Type -> Type where
  IInt : Int -> IToken Int
  ILoc : String -> IToken Id 
  IPlus : IToken Aop
  IMinus : IToken Aop
  IMult : IToken Aop 
  ITrue : IToken String 
  IFalse : IToken String 
  IEqual : IToken Bop
  ILTE : IToken Bop
  INot : IToken ()
  IAnd : IToken Bop2
  IOr : IToken Bop2
  ISkip : IToken String
  IAssign : IToken ()
  ISeq : IToken ()
  IIf : IToken String
  IThen : IToken String
  IElse : IToken String
  IWhile : IToken String
  IDo : IToken String
  ILet : IToken String
  INewLine : IToken ()
  ILparen : IToken ()
  IRParen : IToken ()


lparen : {ct : Vect n Type} -> Grammar ct (IToken ())
lparen = MkGrammar bot (Map (always ILparen) (charSet "("))

rparen : {ct : Vect n Type} -> Grammar ct (IToken ())
rparen = MkGrammar bot (Map (always IRParen) (charSet ")"))


export
intp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (IToken Int)
intp = 
  MkGrammar 
    bot
    (Map 
      (\xs => IInt (cast $ pack xs)) 
      (any 
        [plus digit, 
        MkGrammar
          bot 
          (Map 
            (\(x, xs) => x :: xs) 
            (MkGrammar bot (Seq (charSet "-") (plus digit))))]))


export
truep : {ct : Vect n Type} -> Grammar ct (IToken String)
truep = 
  MkGrammar bot 
  (Map (\_ => ITrue) 
    (MkGrammar bot 
      (Seq 
        (charSet "t") 
        (MkGrammar bot 
          (Seq (charSet "r") 
            (MkGrammar bot (Seq (charSet "u") (charSet "e"))))))))

export
falsep : {ct : Vect n Type} -> Grammar ct (IToken String)
falsep = 
  MkGrammar bot 
  (Map (\_ => IFalse) 
    (MkGrammar bot 
      (Seq 
        (charSet "f") 
        (MkGrammar bot 
          (Seq (charSet "a") 
            (MkGrammar bot 
              (Seq (charSet "l") 
                (MkGrammar bot (Seq (charSet "s") (charSet "e"))))))))))

export
ifp : {ct : Vect n Type} -> Grammar ct (IToken String)
ifp = 
  MkGrammar 
    bot 
    (Map (\_ => IIf) (MkGrammar bot (Seq (charSet "i") (charSet "f"))))


export
thenp : {ct : Vect n Type} -> Grammar ct (IToken String)
thenp = 
  MkGrammar bot 
  (Map (\_ => IThen) 
    (MkGrammar bot 
      (Seq 
        (charSet "t") 
        (MkGrammar bot 
          (Seq (charSet "h") 
            (MkGrammar bot (Seq (charSet "e") (charSet "n"))))))))

export
elsep : {ct : Vect n Type} -> Grammar ct (IToken String)
elsep = 
  MkGrammar bot 
  (Map (\_ => IElse) 
    (MkGrammar bot 
      (Seq 
        (charSet "e") 
        (MkGrammar bot 
          (Seq (charSet "l") 
            (MkGrammar bot (Seq (charSet "s") (charSet "e"))))))))


export
skip : {ct : Vect n Type} -> Grammar ct (IToken String)
skip = 
  MkGrammar bot 
  (Map (\_ => ISkip) 
    (MkGrammar bot 
      (Seq 
        (charSet "s") 
        (MkGrammar bot 
          (Seq (charSet "k") 
            (MkGrammar bot (Seq (charSet "i") (charSet "p"))))))))



export
whilep : {ct : Vect n Type} -> Grammar ct (IToken String)
whilep = 
  MkGrammar bot 
  (Map (\_ => IWhile) 
    (MkGrammar bot 
      (Seq 
        (charSet "w") 
        (MkGrammar bot 
          (Seq (charSet "h") 
            (MkGrammar bot 
              (Seq (charSet "i") 
                (MkGrammar bot (Seq (charSet "l") (charSet "e"))))))))))

export
dop : {ct : Vect n Type} -> Grammar ct (IToken String)
dop = 
  MkGrammar 
    bot 
    (Map (\_ => IDo) (MkGrammar bot (Seq (charSet "d") (charSet "o"))))


export
letp : {ct : Vect n Type} -> Grammar ct (IToken String)
letp = 
  MkGrammar bot 
  (Map (\_ => ILet) 
        (MkGrammar bot 
          (Seq (charSet "l") 
            (MkGrammar bot (Seq (charSet "e") (charSet "t"))))))

export
stp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (IToken Id)
stp = 
  MkGrammar 
    bot
    (Map 
      (\((x, xs)) => ILoc (pack (x :: xs))) 
      (MkGrammar 
        bot 
        (Seq (charSet "`") (plus (any [lower, upper, digit])))))
  -- where 
  --   mapToToken : String -> IToken String
  --   mapToToken "if" = IIf
  --   mapToToken "then" = IThen
  --   mapToToken "else" = IElse
  --   mapToToken "true" = ITrue
  --   mapToToken "false" = IFalse
  --   mapToToken "skip" = ISkip
  --   mapToToken "while" = IWhile
  --   mapToToken "do" = IDo
  --   mapToToken str = ILoc str

 
export
plus : {ct : Vect n Type} -> Grammar ct (IToken Aop)
plus = MkGrammar bot (Map (\_ => IPlus) (charSet "+"))

export
minus : {ct : Vect n Type} -> Grammar ct (IToken Aop)
minus = MkGrammar bot (Map (\_ => IMinus) (charSet "-"))

export
mult : {ct : Vect n Type} -> Grammar ct (IToken Aop)
mult = MkGrammar bot (Map (\_ => IMult) (charSet "*"))

export
equal : {ct : Vect n Type} -> Grammar ct (IToken Bop)
equal = MkGrammar bot (Map (\_ => IEqual) (charSet "="))

export
lte : {ct : Vect n Type} -> Grammar ct (IToken Bop)
lte = 
  MkGrammar 
    bot 
    (Map (\_ => ILTE) (MkGrammar bot (Seq (charSet "<") (charSet "="))))

export
not : {ct : Vect n Type} -> Grammar ct (IToken ())
not = MkGrammar bot (Map (\_ => INot) (charSet "!"))

export
and : {ct : Vect n Type} -> Grammar ct (IToken Bop2)
and = 
  MkGrammar 
    bot 
    (Map (\_ => IAnd) (MkGrammar bot (Seq (charSet "&") (charSet "&"))))

export
or : {ct : Vect n Type} -> Grammar ct (IToken Bop2)
or = 
  MkGrammar 
    bot 
    (Map (\_ => IOr) (MkGrammar bot (Seq (charSet "|") (charSet "|"))))


export
assign : {ct : Vect n Type} -> Grammar ct (IToken ())
assign = 
  MkGrammar 
    bot 
    (Map (\_ => IAssign) (MkGrammar bot (Seq (charSet ":") (charSet "="))))

export
seq : {ct : Vect n Type} -> Grammar ct (IToken ())
seq = MkGrammar bot (Map (\_ => ISeq) (charSet ";"))



data AExp = 
  VInt Int 
  | Loc String 
  | Plus (AExp, AExp) 
  | Minus (AExp, AExp) 
  | Mult (AExp, AExp)

export
Show AExp where
  show y = case y of
              (VInt i) => "VInt " ++ show i
              (Loc id) => "Loc " ++ show id
              (Plus x) => "Plus " ++ show' x
              (Minus x) => "Minus " ++ show' x
              (Mult x) => "Mult " ++ show' x 
    where
      show' : (AExp, AExp) -> String 
      show' (a1, a2) = "(" ++ show a1 ++ ", " ++ show a2 ++ ")"
  
data BExp = 
  VTrue 
  | VFalse 
  | Eq (AExp, AExp) 
  | LTE (AExp, AExp) 
  | Not BExp 
  | And (BExp, BExp)
  | Or (BExp, BExp)


export
Show BExp where 
  show VTrue = "VTrue"
  show VFalse = "VFalse"
  show (Eq x) = "Eq" ++ show x
  show (LTE x) = "LTE " ++ show x
  show (Not x) = "Not " ++ show x
  show (And x) = "And " ++ show' x where 
    show' : (BExp, BExp) -> String 
    show' (b1, b2) = "(" ++ show b1 ++ ", " ++ show b2 ++ ")"
  show (Or x) = "Or " ++ show' x where 
    -- TODO : Repeated , Refactor
    show' : (BExp, BExp) -> String 
    show' (b1, b2) = "(" ++ show b1 ++ ", " ++ show b2 ++ ")"

data Command = 
  Skip 
  | Assign (String, AExp) 
  | Seq (Command, Command) 
  | ITE (BExp, Command, Command) 
  | While (BExp, Command)



export
Show Command where
  show Skip = "Skip"
  show (Assign x) = "Assign " ++ show x
  show (Seq x) = "Seq " ++ show' x where 
    show' : (Command, Command) -> String 
    show' (c1, c2) = "(" ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (ITE x) = "ITE " ++ show' x where 
    show' : (BExp, Command, Command) -> String 
    show' (b, c1, c2) = "(" ++ show b ++ ", " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (While x) = "While " ++ show' x where 
    show' : (BExp, Command) -> String 
    show' (b, c) = "(" ++ show b ++ ", " ++ show c ++ ")"



arith :  {n : Nat} -> {ct : Vect n Type} -> Grammar ct AExp
arith = 
  let int = MkGrammar bot (Map (\(IInt v) => VInt v) intp) 
      -- id = MkGrammar bot (Map (\(ILoc i) => Loc i) stp)
      lis = any [ int]
  in
  MkGrammar 
    bot 
    (Map 
      (\(x, xs) => foldl (\acc, (op , rem) => case op of 
                                            IPlus => Plus (acc, rem)
                                            IMinus => Minus (acc, rem)
                                            IMult => Mult (acc, rem)) x xs) 
      (MkGrammar 
        bot 
        (Seq lis (star (MkGrammar bot (Seq (any [plus, minus, mult]) lis))))))

export
paren : {ct : Vect n Type} -> Grammar ct a -> Grammar ct a
paren p = 
  MkGrammar 
    bot 
    (Map 
      (\((_, a), _) => a) 
      (MkGrammar bot (Seq (MkGrammar bot (Seq lparen p)) rparen)))
      

bool :  {n : Nat} -> {ct : Vect n Type} -> Grammar ct BExp
bool = MkGrammar bot (Fix {a = BExp} bool')
  where
    bool' : {n : Nat} -> {ct' : Vect n Type} -> Grammar (BExp :: ct') BExp
    bool' = 
      let true = MkGrammar bot (Map (\_ => VTrue) truep) 
          false = MkGrammar bot (Map (\_ => VFalse) falsep) 
          eq = MkGrammar 
                bot 
                (Map 
                  (\(a1, (op, a2)) => case op of 
                                          IEqual => Eq (a1, a2)
                                          ILTE => LTE (a1, a2)) 
                  (MkGrammar 
                    bot 
                    (Seq 
                      (arith)
                      (MkGrammar bot (Seq (any [equal, lte]) arith)))))
          te = any [paren (MkGrammar bot (Var Z)), true, false, eq]
          nt = MkGrammar 
                  bot 
                  (Map 
                    (\(_, xs) => Not xs) 
                    (MkGrammar bot (Seq not te)))
          tes =   MkGrammar 
                    bot 
                    (Map 
                      (\(x, xs) => foldl (\acc, (op , rem) => case op of 
                                                            IAnd => And (acc, rem)
                                                            IOr => Or (acc, rem)) x xs) 
                      (MkGrammar 
                        bot 
                        (Seq (te) (star (MkGrammar bot (Seq (any [and, or]) (any [te, nt])))))))
          ntes =   MkGrammar 
                    bot 
                    (Map 
                      (\(x, xs) => foldl (\acc, (op , rem) => case op of 
                                                            IAnd => And (acc, rem)
                                                            IOr => Or (acc, rem)) x xs) 
                      (MkGrammar 
                        bot 
                        (Seq (nt) (star (MkGrammar bot (Seq (any [and, or]) (any [te, nt])))))))
      in
      any [ntes, tes]

command : Grammar Nil Command
command = MkGrammar bot (Fix {a = Command} command')
  where
    command' : Grammar [Command] Command
    command' = 
      let skip = MkGrammar bot (Map (\_ => Skip) skip)
          assign = MkGrammar 
                    bot 
                    (Map 
                      (\(_, (ILoc id, (_, aexp))) => Assign (id, aexp)) 
                      (MkGrammar bot (Seq letp (MkGrammar bot (Seq stp (MkGrammar bot (Seq assign arith))))))) 
          ite = MkGrammar 
                bot 
                (Map 
                  (\(_, (b, (_, (c1, (_, c2))))) => ITE (b, c1, c2))  
                  (MkGrammar 
                    bot 
                    (Seq 
                      (ifp) 
                      (MkGrammar 
                        bot 
                        (Seq 
                          (bool) 
                          (MkGrammar 
                            bot 
                            (Seq 
                              (thenp) 
                              (MkGrammar 
                                bot 
                                (Seq 
                                  (MkGrammar bot (Var Z)) 
                                  (MkGrammar 
                                    bot 
                                    (Seq elsep (MkGrammar bot (Var Z)))))))))))))
          wd = MkGrammar 
                bot 
                (Map 
                  (\(_, (b, (_, c))) => While (b, c))  
                  (MkGrammar 
                    bot 
                    (Seq 
                      (whilep) 
                      (MkGrammar 
                        bot 
                        (Seq 
                          (bool) 
                          (MkGrammar 
                            bot 
                            (Seq (dop) (MkGrammar bot (Var Z)))))))) )
          lis = any [paren (MkGrammar bot (Var Z)), skip, assign]
          tes =   MkGrammar 
                    bot 
                    (Map 
                      (\(x, xs) => foldl (\acc, (_ , rem) => Seq (acc, rem)) x xs) 
                      (MkGrammar 
                        bot 
                        (Seq (lis) (star (MkGrammar bot (Seq seq (lis)))))))
      in
      any [wd, ite, tes]


export 
parsemb : String -> Either String (BExp, List Char)
parsemb input = 
  do
    parser <- generateParser bool 
    parser (unpack input)

export 
parsec : String -> Either String (Command, List Char)
parsec input = 
  do
    parser <- generateParser command 
    parser (unpack input)

export 
parsea : String -> Either String (AExp, List Char)
parsea input = 
  do
    parser <- generateParser arith 
    parser (unpack input)