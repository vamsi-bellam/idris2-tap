module Examples.Imp

import Data.Vect
import Data.String

import Grammar
import Var
import Parser
import Token

import Examples.Utils

%hide Prelude.Ops.infixr.(<|>)

{- 

Arithmetic Expressions 

a ::= n | X | a0 + a1 | a0 - a1 | a0 * a1

Boolean Expressions 

b ::= true | false | a0 = a1 | a0 <= a1 | !b | b0 && b1 | b0 || b1 | (b)

Commands 

c ::= skip | X := a | c0;c1 | if b then c0 else c1 done 
      | while b do c done | (c)

-}

keywords : Vect 9 String
keywords = 
  ["if"
  , "then"
  , "else"
  , "true"
  , "false"
  , "skip"
  , "while"
  , "do"
  , "done"
  ]

data Aop = APlus | AMinus | AMult
data Acmp = ALte | AEq
data Bop = BAnd | BOr

data IToken : Type -> Type where
  IInt : IToken Int
  ILoc : IToken String
  IPlus : IToken Aop
  IMinus : IToken Aop
  IMult : IToken Aop 
  ITrue : IToken () 
  IFalse : IToken () 
  IEqual : IToken Acmp
  ILTE : IToken Acmp
  INot : IToken ()
  IAnd : IToken Bop
  IOr : IToken Bop
  ISkip : IToken ()
  IAssign : IToken ()
  ISeq : IToken ()
  IIf : IToken ()
  IThen : IToken ()
  IElse : IToken ()
  IDone : IToken ()
  IWhile : IToken ()
  IDo : IToken ()
  ILparen : IToken ()
  IRParen : IToken ()

Tag IToken where
  compare IInt     IInt     = Eql
  compare IInt     _        = Leq
  compare _        IInt     = Geq

  compare ILoc     ILoc     = Eql
  compare ILoc     _        = Leq
  compare _        ILoc     = Geq

  compare IPlus    IPlus    = Eql
  compare IPlus    _        = Leq
  compare _        IPlus    = Geq

  compare IMinus   IMinus   = Eql
  compare IMinus   _        = Leq
  compare _        IMinus   = Geq

  compare IMult    IMult    = Eql
  compare IMult    _        = Leq
  compare _        IMult    = Geq

  compare ITrue    ITrue    = Eql
  compare ITrue    _        = Leq
  compare _        ITrue    = Geq

  compare IFalse   IFalse   = Eql
  compare IFalse   _        = Leq
  compare _        IFalse   = Geq

  compare IEqual   IEqual   = Eql
  compare IEqual   _        = Leq
  compare _        IEqual   = Geq

  compare ILTE     ILTE     = Eql
  compare ILTE     _        = Leq
  compare _        ILTE     = Geq

  compare INot     INot     = Eql
  compare INot     _        = Leq
  compare _        INot     = Geq

  compare IAnd     IAnd     = Eql
  compare IAnd     _        = Leq
  compare _        IAnd     = Geq

  compare IOr      IOr      = Eql
  compare IOr      _        = Leq
  compare _        IOr      = Geq

  compare ISkip    ISkip    = Eql
  compare ISkip    _        = Leq
  compare _        ISkip    = Geq

  compare IAssign  IAssign  = Eql
  compare IAssign  _        = Leq
  compare _        IAssign  = Geq

  compare ISeq     ISeq     = Eql
  compare ISeq     _        = Leq
  compare _        ISeq     = Geq

  compare IIf      IIf      = Eql
  compare IIf      _        = Leq
  compare _        IIf      = Geq

  compare IThen    IThen    = Eql
  compare IThen    _        = Leq
  compare _        IThen    = Geq

  compare IElse    IElse    = Eql
  compare IElse    _        = Leq
  compare _        IElse    = Geq

  compare IDone    IDone    = Eql
  compare IDone    _        = Leq
  compare _        IDone    = Geq

  compare IWhile   IWhile   = Eql
  compare IWhile   _        = Leq
  compare _        IWhile   = Geq

  compare IDo      IDo      = Eql
  compare IDo      _        = Leq
  compare _        IDo      = Geq

  compare ILparen  ILparen  = Eql
  compare ILparen  _        = Leq
  compare _        ILparen  = Geq

  compare IRParen  IRParen  = Eql
  compare IRParen  _        = Leq
  compare _        IRParen  = Geq


  show IInt     = "IInt"
  show ILoc     = "ILoc"
  show IPlus    = "IPlus"
  show IMinus   = "IMinus"
  show IMult    = "IMult"
  show ITrue    = "ITrue"
  show IFalse   = "IFalse"
  show IEqual   = "IEqual"
  show ILTE     = "ILTE"
  show INot     = "INot"
  show IAnd     = "IAnd"
  show IOr      = "IOr"
  show ISkip    = "ISkip"
  show IAssign  = "IAssign"
  show ISeq     = "ISeq"
  show IIf      = "IIf"
  show IThen    = "IThen"
  show IElse    = "IElse"
  show IDone    = "IDone"
  show IWhile   = "IWhile"
  show IDo      = "IDo"
  show ILparen  = "ILparen"
  show IRParen  = "IRParen"



lparen : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
lparen = char '(' $$ always (Tok ILparen ()) 

rparen : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
rparen = char ')' $$ always (Tok IRParen ())

intp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
intp = plus digit $$ (\xs => Tok IInt (cast $ pack xs))

stp : {n : Nat} -> {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
stp = (any [lower, upper] >>> star (any [lower, upper, digit]))
      $$ (\((x, xs)) => toToken $ pack (x :: xs))
  where 
    toToken : String -> Token IToken
    toToken "if" = Tok IIf ()
    toToken "then" = Tok IThen ()
    toToken "else" = Tok IElse ()
    toToken "done" = Tok IDone ()
    toToken "true" = Tok ITrue ()
    toToken "false" = Tok IFalse ()
    toToken "skip" = Tok ISkip ()
    toToken "while" = Tok IWhile ()
    toToken "do" = Tok IDo ()
    toToken str = Tok ILoc str

plus : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
plus = char '+' $$ always (Tok IPlus APlus)

minus : {n : Nat } -> {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
minus = ((char '-') >>> (maybe (plus digit))) $$ toToken

  where
    toToken : (Char, Maybe (List Char)) -> (Token IToken)
    toToken (x, Nothing) = Tok IMinus AMinus
    toToken (x, (Just rest)) = Tok IInt (cast $ pack (x :: rest))

mult : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
mult = char '*' $$ always (Tok IMult AMult) 

equal : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
equal = char '=' $$ always (Tok IEqual AEq)

lte : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
lte = (char '<' >>> char '=') $$ always (Tok ILTE ALte)

not : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
not = char '!' $$ always (Tok INot ()) 

and : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
and = (char '&' >>> char '&') $$ always (Tok IAnd BAnd)

or : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
or = (char '|' >>> char '|') $$ always (Tok IOr BOr)

assign : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
assign = (char ':' >>> char '=') $$  always (Tok IAssign ())

seq : {ct : Vect n Type} -> Grammar ct (Token IToken) CharTag
seq = char ';' $$ always (Tok ISeq ()) 

impToken : Grammar Nil (Token IToken) CharTag
impToken = fix impToken'

  where
    impToken' : Grammar [Token IToken] (Token IToken) CharTag
    impToken' = 
      any 
        [ lparen
        , rparen
        , intp
        , stp
        , plus
        , minus
        , mult
        , equal
        , lte
        , not
        , and
        , or
        , assign
        , seq
        , skipSpace (var Z)
        ]


public export
data AExp = 
  VInt Int 
  | Loc String 
  | Plus (AExp, AExp) 
  | Minus (AExp, AExp) 
  | Mult (AExp, AExp)

Eq AExp where 
  (VInt i) == (VInt j) = i == j
  (Loc id1) == (Loc id2) =  id1 == id2
  (Plus (a1, a2)) == (Plus (b1, b2)) = (a1 == b1 && a2 == b2)
  (Minus (a1, a2)) == (Minus (b1, b2)) =  (a1 == b1 && a2 == b2)
  (Mult (a1, a2)) == (Mult (b1, b2)) = (a1 == b1 && a2 == b2)
  _ == _ = False

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

public export 
data BExp = 
  VTrue 
  | VFalse 
  | Eq (AExp, AExp) 
  | LTE (AExp, AExp) 
  | Not BExp 
  | And (BExp, BExp)
  | Or (BExp, BExp)

Eq BExp where
  VTrue == VTrue = True
  VFalse == VFalse = True
  (Eq (a1, a2)) == (Eq (b1, b2)) = (a1 == b1 && a2 == b2)
  (LTE (a1, a2)) == (LTE (b1, b2)) = (a1 == b1 && a2 == b2)
  (Not x) == (Not y) = x == y
  (And (a1, a2)) == (And (b1, b2)) = (a1 == b1 && a2 == b2)
  (Or (a1, a2)) == (Or (b1, b2)) = (a1 == b1 && a2 == b2)
  _ == _ = False

export
Show BExp where 
  show VTrue = "VTrue"
  show VFalse = "VFalse"
  show (Eq x) = "Eq" ++ showParens True (show x)
  show (LTE x) = "LTE " ++ showParens True (show x)
  show (Not x) = "Not " ++ showParens True (show x)
  show (And x) = "And " ++ show' x where 
    show' : (BExp, BExp) -> String 
    show' (b1, b2) = "(" ++ show b1 ++ ", " ++ show b2 ++ ")"
  show (Or x) = "Or " ++ show' x where 
    show' : (BExp, BExp) -> String 
    show' (b1, b2) = "(" ++ show b1 ++ ", " ++ show b2 ++ ")"

public export
data Command = 
  Skip 
  | Assign (String, AExp) 
  | Seq (Command, Command) 
  | ITE (BExp, Command, Command) 
  | While (BExp, Command)

export
Eq Command where
  Skip == Skip = True
  (Assign x) == (Assign y) = x == y
  (Seq (a1, a2)) == (Seq (b1, b2)) = (a1 == b1 && a2 == b2)
  (ITE (b, c1, c2)) == (ITE (b', c3, c4)) = (b == b' && c1 == c3 && c2 == c4)
  (While (b1, c1)) == (While (b2, c2)) = (b1 == b2 && c1 == c2)
  _ == _ = False

export
Show Command where
  show Skip = "Skip"
  show (Assign x) = "Assign " ++ show x
  show (Seq x) = "Seq " ++ show' x where 
    show' : (Command, Command) -> String 
    show' (c1, c2) = "(" ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (ITE x) = "ITE " ++ show' x where 
    show' : (BExp, Command, Command) -> String 
    show' (b, c1, c2) = 
      "(" ++ show b ++ ", " ++ show c1 ++ ", " ++ show c2 ++ ")"
  show (While x) = "While " ++ show' x where 
    show' : (BExp, Command) -> String 
    show' (b, c) = "(" ++ show b ++ ", " ++ show c ++ ")"

paren : {a : Type} 
     -> {n : Nat} 
     -> {ct : Vect n Type} 
     -> Grammar ct a IToken 
     -> Grammar ct a IToken
paren p = between (tok ILparen) p (tok IRParen)
 
arith :  {n : Nat} -> {ct : Vect n Type} -> Grammar ct AExp IToken
arith =  fix arith'

  where 
    arith' : {n : Nat} 
          -> {ct' : Vect n Type} 
          -> Grammar (AExp :: ct') AExp IToken
    arith' = 
      let int = tok IInt $$ VInt
          id = tok ILoc $$ Loc
          toks = any [int, id]
      in (toks >>> maybe (any [tok IPlus, tok IMinus, tok IMult] >>> var Z)) $$ 
          toAExp
      
      where 
        toAExp : (AExp, Maybe (Aop, AExp)) -> AExp
        toAExp (x, Nothing) = x
        toAExp (x, Just (APlus, z)) = Plus (x, z)
        toAExp (x, Just (AMinus, z)) = Minus (x, z)
        toAExp (x, Just (AMult, Plus(a1, a2))) = Plus ((Mult (x, a1), a2))
        toAExp (x, Just (AMult, Minus(a1, a2))) = Minus (Mult (x, a1), a2)
        toAExp (x, Just (AMult, z)) = Mult (x, z)


bool :  {n : Nat} -> {ct : Vect n Type} -> Grammar ct BExp IToken
bool = fix bool'
  where
    bool' : {n : Nat} 
         -> {ct' : Vect n Type} 
         -> Grammar (BExp :: ct') BExp IToken
    bool' = 
      let true = tok ITrue $$ always VTrue 
          false = tok IFalse $$ always VFalse
          eq =  (arith >>> any [tok IEqual, tok ILTE] >>> arith) $$ 
                (\((a1, op), a2) => case op of 
                                        AEq => Eq (a1, a2)
                                        ALte => LTE (a1, a2))
          te = any [paren (var Z), true, false, eq]
          nt = (tok INot >>> te) $$  (\(_, xs) => Not xs)
          tes = (te >>> (star (any [tok IAnd, tok IOr] >>> any [te, nt]))) $$
                (\(x, xs) => 
                      foldl (\acc, (op , rem) => 
                        case op of 
                              BAnd => And (acc, rem)
                              BOr => Or (acc, rem)) x xs) 
          ntes = (nt >>> (star (any [tok IAnd, tok IOr] >>> any [te, nt]))) $$
                 (\(x, xs) => 
                        foldl (\acc, (op , rem) =>
                          case op of 
                                BAnd => And (acc, rem)
                                BOr => Or (acc, rem)) x xs) 
      in
      any [tes, ntes]


command : Grammar Nil Command IToken
command = fix command'
  where
    command' : Grammar [Command] Command IToken
    command' = (any [baseCommand, paren baseCommand] 
                >>> maybe (tok ISeq >>> var Z)) $$ 
                (\(b, ms) => case ms of
                                  Nothing => b
                                  Just (_, c) => Seq (b, c))
    where
     baseCommand : Grammar [Command] Command IToken
     baseCommand = 
      let skip    = tok ISkip $$ always Skip 
          assign  = (tok ILoc >>> tok IAssign >>> arith) $$ 
                   (\((id, _), aexp) => Assign (id, aexp)) 
          ifelse  = (tok IIf >>> bool >>> tok IThen >>> var Z >>> tok IElse >>> 
                    var Z >>> tok IDone) $$ 
                    (\(((((((_, b), _), c1), _), c2), _)) => ITE (b, c1, c2))
          whiledo = (tok IWhile >>> bool >>> tok IDo >>> var Z >>> tok IDone) $$ 
                    (\(((((_, b), _), c), _)) => While (b, c))
      in any [skip, assign, whiledo, ifelse]

export 
parseArith : String -> Either String AExp
parseArith input = do 
  lexedTokens <- lexer impToken input
  parser arith lexedTokens

export 
parseBool : String -> Either String BExp
parseBool input = do 
  lexedTokens <- lexer impToken input
  parser bool lexedTokens

export 
parseCommand : String -> Either String Command
parseCommand input = do 
  lexedTokens <- lexer impToken (trim input)
  parser command lexedTokens