{-
  (c) 2018 Copyright Martin Baker
  I would prefer GPL3 licence but if there were any interest in including
  this with Idris library then a compatible licence would be acceptable.
  
  This code attempts to implement expressions using Idris.
  This allows us to work with variables.
  For an explanation with example session see this page:
  http://www.euclideanspace.com/prog/idris/expressions/index.htm
  for more general information about objectives see this page:
  http://www.euclideanspace.com/prog/idris/
-}

module fieldexp

%access public export

||| Expression over a field
data ExpressionField = ||| literal value
   LitFloat Double
  | ||| variable
   VarFloat String
  | ||| add
   (+) ExpressionField ExpressionField
  | ||| subtract
   (-) ExpressionField ExpressionField
  | ||| multiply
   (*) ExpressionField ExpressionField
  | ||| divide
   (/) ExpressionField ExpressionField
  | ||| function
   Function String (List ExpressionField)
  | ||| unknown
   Undefined

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
Eq ExpressionField where
  (==) (LitFloat a) (LitFloat b) = a==b
  (==) (VarFloat a) (VarFloat b) = a==b
  (==) ((+) a b) ((+) c d) = (a==c) && (b==d)
  (==) ((-) a b) ((-) c d) = (a==c) && (b==d)
  (==) ((*) a b) ((*) c d) = (a==c) && (b==d)
  (==) ((/) a b) ((/) c d) = (a==c) && (b==d)
  (==) (Function a b) (Function c d) = (a==c) && (eqList b d) where
    eqList : (List ExpressionField) -> (List ExpressionField) -> Bool
    eqList [] [] = True
    eqList [] (b::bs) = False
    eqList (a::as) [] = False
    eqList (a::as) (b::bs) = (a==b) && (eqList as bs)
  (==) Undefined Undefined = True
  (==) _ _ = False

||| No way to do this because we don't know value of variable
Ord ExpressionField where
  compare x y = EQ

||| make ExpressionField implement Num
Num ExpressionField where
  (+) a b = a + b
  (*) a b = a * b
  fromInteger x = Function "fromint" [Undefined]

||| make ExpressionField implement Neg
Neg ExpressionField where
  negate x = Function "negate" [x]
  (-) a b = a - b

Fractional ExpressionField where
  (/) a b = a / b
  recip a = (LitFloat 1.0) / a

Show ExpressionField where
  show (LitFloat a) = prim__floatToStr a
  show (VarFloat a) = a
  show ((+) a b) = (show a) ++ "+" ++ (show b)
  show ((-) a b) = (show a) ++ "-" ++ (show b)
  show ((*) a b) = (show a) ++ "*" ++ (show b)
  show ((/) a b) = (show a) ++ "/" ++ (show b)
  show (Function a b) = (show a) ++ "("  ++ (showList b) ++ ")" where
    showList : (List ExpressionField) -> String
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

||| Implementation of FieldIfce over ExpressionField
||| which contains variables in addition to functions and numbers.
FieldIfce ExpressionField where
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
  specialDouble v = if isZro v then DZero ExpressionField v else
                    if isOne v then DOne ExpressionField v else
                      DOther ExpressionField v
  simplify a = simplifyn 0 a where
   simplifyn : Nat -> ExpressionField -> ExpressionField
   simplifyn n a =
     let b=simplify1 a
     in if n>4 
        then b
        else
          if a==b then a else simplifyn (n+1) b
            where
    simplify1 : ExpressionField -> ExpressionField
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
      simplifyList : (List ExpressionField) -> (List ExpressionField)
      simplifyList [] = []
      simplifyList (c::cs) = (simplify1 c)::(simplifyList cs)
    simplify1 Undefined = Undefined
