{- (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 licence but if there were any interest in including
 - this with Idris library then a compatible licence would be acceptable.
 - 
 - This code attempts to implement expressions using Idris.
 - This allows us to work with variables.
 - For an explanation with example session see this page:
 - http://www.euclideanspace.com/prog/idris/expressions/index.htm
 - for more general information about objectives see this page:
 - http://www.euclideanspace.com/prog/idris/
 -}

||| modles an epresiion which may have variables that are fields
module fieldexp

%access public export

{- In order to implement an algebra our expressions and equations
 - need to work with mathematical variables. Note these variables
 - are different from variabes in a program, for instance,
 - 'y = 2*x' does not mean 'take the current value of x, multiply
 - it by 2 and assign this value to y' instead it means 'x and y
 - can range over any values as long as y is always twice x'.
 - 
 - Idealy I would want to have an expression over mixed types.
 - For instance I would like have Doubles and Integers in the
 - same expression, also vectors and scalars in the same
 - expression, in fact any mathematically valid combination
 - of types.
 -
 - So I would like to generalise the current implementation
 - from an 'Expression over a field' to 'Expression over a
 - mathematical type'. However
 - this means that, for instance,  the (/) is not valid for
 - certain types so we want to bar that operator for types
 - where it is not valid. Also these types would not implement
 - the Fractional interface and so on.
 -
 - I don't know how to code this so the Idris type system could
 - allow and disallow these things for each mathematical type
 - in the expression.
 -
 - Another enhancement that I would like is to code variables
 - using de Bruijn indexes as in 'The Well-Typed Interpreter'
 - example here:
 - http://docs.idris-lang.org/en/latest/tutorial/interp.html
 -}
||| Expression over a field.
||| An expression can contain both literal values and variables
||| and therefore the result of functions and binary operations
||| cannot always be reduced down to a single number so the
||| value of Expression fld can be a tree structure.
data Expression fld = ||| literal float value
   LitFloat fld
  | ||| variable
   VarFloat String
  | ||| add
   (+) (Expression fld) (Expression fld)
  | ||| subtract
   (-) (Expression fld) (Expression fld)
  | ||| multiply
   (*) (Expression fld) (Expression fld)
  | ||| divide
   (/) (Expression fld) (Expression fld)
  | ||| function
   Function String (List (Expression fld))
  | ||| unknown
   Undefined

{- It is unfortunate that '=' is built into the Idris language.
 - In the Idris language it is used much more like an assignment
 - and a better symbol for that would be ':='. I would prefer
 - '=' to be used for equations.
 -
 - (===) needs to bind more tightly than the expressions
 - on either side of it.
 -}
||| An equation contains an equals sign and a left hand side
||| expression and a right hand side expression.
||| We have to use (===) for the equals sign because (=) and
||| (==) are already used.
record Equation fld where
  constructor (===)
  lhs:flt
  rhs:flt

||| We need to treat 0.0 and 1.0 differently from other
||| floating point values. For instance we want to simplify
||| x+0.0 to x and we need to avoid 0.0 in divisor. We therefore
||| have this view type which can match on particular Double values
data SpecialDouble : (ty:Type) -> (x:ty) -> Type where
  DZero: (ty:Type) -> (x:ty) -> SpecialDouble ty x
  DOne: (ty:Type) -> (x:ty) -> SpecialDouble ty x
  DOther: (ty:Type) -> (x:ty) -> SpecialDouble ty x

||| Can't compare values, in general,  because we don't know value
||| of variable so we just check both sides have same structure.
Eq (Expression Double) where
  (==) (LitFloat a) (LitFloat b) = a==b
  (==) (VarFloat a) (VarFloat b) = a==b
  (==) ((+) a b) ((+) c d) = (a==c) && (b==d)
  (==) ((-) a b) ((-) c d) = (a==c) && (b==d)
  (==) ((*) a b) ((*) c d) = (a==c) && (b==d)
  (==) ((/) a b) ((/) c d) = (a==c) && (b==d)
  (==) (Function a b) (Function c d) = (a==c) && (eqList b d) where
    eqList : (List (Expression Double)) -> (List (Expression Double)) -> Bool
    eqList [] [] = True
    eqList [] (b::bs) = False
    eqList (a::as) [] = False
    eqList (a::as) (b::bs) = (a==b) && (eqList as bs)
  (==) Undefined Undefined = True
  (==) _ _ = False

||| No way to do this because we don't know value of variable
Ord (Expression Double) where
  compare x y = EQ

||| make (Expression Double) implement Num
Num (Expression Double) where
  (+) a b = a + b
  (*) a b = a * b
  fromInteger a = Function "fromint" [LitFloat (fromInteger a)]

||| make (Expression Double) implement Neg
Neg (Expression Double) where
  negate a = Function "negate" [a]
  (-) a b = a - b

Fractional (Expression Double) where
  (/) a b = a / b
  recip a = (LitFloat 1.0) / a

Show (Expression Double) where
  show (LitFloat a) = prim__floatToStr a
  show (VarFloat a) = a
  show ((+) a b) = (show a) ++ "+" ++ (show b)
  show ((-) a b) = (show a) ++ "-" ++ (show b)
  show ((*) a b) = (show a) ++ "*" ++ (show b)
  show ((/) a b) = (show a) ++ "/" ++ (show b)
  show (Function a b) = (show a) ++ "("  ++ (showList b) ++ ")" where
    showList : (List (Expression Double)) -> String
    showList [] = ""
    showList (c::cs) = (show c) ++ "::" ++ (showList cs)
  show Undefined = " undefined "

||| Define the mathematical structures over a field.
||| Not just Float or Double but also variables (to implement
||| algebra).
interface (Neg ty, Fractional ty, Ord ty,Eq ty, Show ty) => FieldIfce ty where
  sqrt : ty -> ty
  Zro : ty
  One : ty
  isZro : ty -> Bool
  isOne : ty -> Bool
  --ifThenElse : Bool -> Lazy ty -> Lazy ty -> ty
  simplify : ty -> ty
  evaluate : ty -> String -> ty
  ||| Covering function for SpecialDouble
  specialDouble : (v:ty) -> SpecialDouble ty v
    
||| Implementation of FieldIfce over Double
||| Use this when we just need a numerical result without
||| any variables.
FieldIfce Double where
  sqrt x = prim__floatSqrt x
  Zro = 0.0
  One = 1.0
  isZro x = boolOp prim__eqFloat x 0.0
  isOne x = boolOp prim__eqFloat x 1.0
  --ifThenElse True  t e = t
  --ifThenElse False t e = e
  simplify a = a
  evaluate a b = a
  specialDouble v = if isZro v then DZero Double v else
                    if isOne v then DOne Double v else
                      DOther Double v

{- Notes about floating point equality and matching.
 -
 - Pattern matching on floating point and testing equality on floating
 - point are both problematic.
 -
 - I would like to do this:
 -  simplify ((+) a (LitFloat 0.0)) = simplify a
 -
 - This works fine in REPL but causes following error in
 - test framework:
 -
 - Type checking /tmp/idris1194953865894429689.idr
 - Can't match on (0.0)
 - Uncaught error: /tmp/idris21033187761597322404:
 - rawSystem: runInteractiveProcess: exec: permission denied
 -(Permission denied)                                                         
 -}

||| Implementation of FieldIfce over Expression Double
||| which contains variables in addition to functions and numbers.
FieldIfce (Expression Double) where
  sqrt x = Function "sqrt" [x]
  Zro = LitFloat 0.0
  One = LitFloat 1.0
  isZro (LitFloat 0.0) = True
  isZro _ = False
  isOne (LitFloat 1.0) = True
  isOne _ = False
  --ifThenElse True  t e = Undefined
  --ifThenElse False t e = Undefined
  evaluate a b = a
  specialDouble v = if isZro v then DZero (Expression Double) v else
                    if isOne v then DOne (Expression Double) v else
                      DOther (Expression Double) v
  simplify a = simplifyn 0 a where
   simplifyn : Nat -> (Expression Double) -> (Expression Double)
   simplifyn n a =
     let b=simplify1 a
     in if n>4 
        then b
        else
          if a==b then a else simplifyn (n+1) b
            where
    simplify1 : (Expression Double) -> (Expression Double)
    simplify1 (LitFloat a) = LitFloat a
    simplify1 (VarFloat s) = VarFloat s
    simplify1 ((+) (LitFloat a) (LitFloat b)) = LitFloat (Prelude.Interfaces.(+) a b)
    simplify1 ((+) Undefined b) = Undefined
    simplify1 ((+) a Undefined) = Undefined
    simplify1 ((+) (LitFloat n) b) = if isZro(n) then simplify1 b
                                else fieldexp.(+) (LitFloat n) (simplify1 b)
    simplify1 ((+) a (LitFloat n)) = if isZro(n) then simplify1 a
                                else fieldexp.(+) (simplify1 a) (LitFloat n)
    simplify1 ((+) a b) = if a == b then
              (*) (LitFloat 2.0) (simplify1 a) else fieldexp.(+) (simplify1 a) (simplify1 b)
    simplify1 ((-) (LitFloat a) (LitFloat b)) = LitFloat (Prelude.Interfaces.(-) a b)
    simplify1 ((-) Undefined b) = Undefined
    simplify1 ((-) a Undefined) = Undefined
    simplify1 ((-) (LitFloat n) b) = if isZro(n) then -(simplify1 b)
                                else fieldexp.(-) (LitFloat n) (simplify1 b)
    simplify1 ((-) a (LitFloat n)) = if isZro(n) then simplify1 a
                                else fieldexp.(-) (simplify1 a) (LitFloat n)
    simplify1 ((-) a b) = if a == b then
               LitFloat 0.0 else fieldexp.(-) (simplify1 a) (simplify1 b)
    simplify1 ((*) (LitFloat a) (LitFloat b)) = LitFloat (Prelude.Interfaces.(*) a b)
    simplify1 ((*) Undefined b) = Undefined
    simplify1 ((*) a Undefined) = Undefined
    simplify1 ((*) (LitFloat n) b) = if isOne(n)
                                then simplify1 b
                                else 
                                  if isZro(n)
                                  then LitFloat 0.0
                                  else fieldexp.(*) (LitFloat n) (simplify1 b)
    simplify1 ((*) a (LitFloat n)) = if isOne(n)
                                then simplify1 a
                                else 
                                  if isZro(n)
                                  then LitFloat 0.0
                                  else fieldexp.(*) (simplify1 a) (LitFloat n)
    simplify1 ((*) a b) = if a == b then
               Function "sqr" [simplify1 a] else fieldexp.(*) (simplify1 a) (simplify1 b)
    simplify1 ((/) (LitFloat a) (LitFloat b)) = LitFloat (Prelude.Interfaces.(/) a b)
    simplify1 ((/) Undefined b) = Undefined
    simplify1 ((/) a Undefined) = Undefined
    simplify1 ((/) (LitFloat n) b) = if isOne(n) then Function "inv" [simplify1 b]
                                else fieldexp.(/) (LitFloat n) (simplify1 b)
    simplify1 ((/) a (LitFloat n)) = if isOne(n) then simplify1 a
                                else fieldexp.(/) (simplify1 a) (LitFloat n)
    simplify1 ((/) a b) = if a == b then
               LitFloat 1.0 else fieldexp.(/) (simplify1 a) (simplify1 b)
    -- I want to do:
    --simplify1 (Function a b) = Function a (map simplify1 b)
    -- but this is not proved to be total so, for now, impement
    -- local simplifyList function:
    simplify1 (Function a b) = Function a (simplifyList b) where
      simplifyList : (List (Expression Double)) -> (List (Expression Double))
      simplifyList [] = []
      simplifyList (c::cs) = (simplify1 c)::(simplifyList cs)
    simplify1 Undefined = Undefined
