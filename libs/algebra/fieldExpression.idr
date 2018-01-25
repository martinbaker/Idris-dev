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
   ExpFld Double
  | ||| variable
   Var String
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
  (==) (ExpFld a) (ExpFld b) = a==b
  (==) (Var a) (Var b) = a==b
  (==) ((+) a b) ((+) c d) = (a==c) && (b==d)
  (==) ((-) a b) ((-) c d) = (a==c) && (b==d)
  (==) ((*) a b) ((*) c d) = (a==c) && (b==d)
  (==) ((/) a b) ((/) c d) = (a==c) && (b==d)
  --cant compare lists due to recursive nature
  --(==) (Function a b) (Function c d) = (a==c) && (b==d)
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
  recip a = (ExpFld 1.0) / a

Show ExpressionField where
  show (ExpFld a) = prim__floatToStr a
  show (Var a) = a
  show ((+) a b) = (show a) ++ "+" ++ (show b)
  show ((-) a b) = (show a) ++ "-" ++ (show b)
  show ((*) a b) = (show a) ++ "*" ++ (show b)
  show ((/) a b) = (show a) ++ "/" ++ (show b)
  show (Function a b) = (show a) ++ "(" -- ++ (show b) ++ ")"
  -- show b (which is a list) causes problems
  show Undefined = " undefined "

||| Define the mathematical structures over a field.
||| Not just Float or Double but also variables (to implement
||| algebra).
interface (Neg ty, Fractional ty, Ord ty,Eq ty, Show ty) => FieldIfce ty where
  --(==) : ty -> ty -> Bool
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
  --(==) = boolOp prim__eqFloat
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


||| Implementation of FieldIfce over ExpressionField
||| which contains variables in addition to functions and numbers.
FieldIfce ExpressionField where
  sqrt x = Function "sqrt" [x]
  Zro = ExpFld 0.0
  One = ExpFld 1.0
  isZro (ExpFld 0.0) = True
  isZro _ = False
  isOne (ExpFld 1.0) = True
  isOne _ = False
  --ifThenElse True  t e = Undefined
  --ifThenElse False t e = Undefined
  evaluate a b = a
  specialDouble v = if isZro v then DZero ExpressionField v else
                    if isOne v then DOne ExpressionField v else
                      DOther ExpressionField v
  simplify (ExpFld a) = ExpFld a
  simplify (Var s) = Var s
  simplify ((+) (ExpFld a) (ExpFld b)) = ExpFld (Prelude.Interfaces.(+) a b)
  -- following works fine in REPL but causes following error in
  -- test framework: 
  -- Type checking /tmp/idris1194953865894429689.idr
  -- Can't match on (0.0)
  -- Uncaught error: /tmp/idris21033187761597322404:
  -- rawSystem: runInteractiveProcess: exec: permission denied
  --(Permission denied)                                                         
  --  simplify ((+) (ExpFld 0.0) b) = simplify b
  --  simplify ((+) a (ExpFld 0.0)) = simplify a
  simplify ((+) (ExpFld n) b) = if isZro(n) then simplify b
                                else fieldexp.(+) (ExpFld n) (simplify b)
  simplify ((+) a (ExpFld n)) = if isZro(n) then simplify a
                                else fieldexp.(+) (simplify a) (ExpFld n)
  simplify ((+) a b) = if a == b then
              (*) (ExpFld 2.0) (simplify a) else fieldexp.(+) (simplify a) (simplify b)
  simplify ((-) (ExpFld a) (ExpFld b)) = ExpFld (Prelude.Interfaces.(-) a b)
--  simplify ((-) (ExpFld 0.0) b) = -(simplify b)
--  simplify ((-) a (ExpFld 0.0)) = simplify a
  simplify ((-) (ExpFld n) b) = if isZro(n) then -(simplify b)
                                else fieldexp.(-) (ExpFld n) (simplify b)
  simplify ((-) a (ExpFld n)) = if isZro(n) then simplify a
                                else fieldexp.(-) (simplify a) (ExpFld n)
  simplify ((-) a b) = if a == b then
               ExpFld 0.0 else fieldexp.(-) (simplify a) (simplify b)
  simplify ((*) (ExpFld a) (ExpFld b)) = ExpFld (Prelude.Interfaces.(*) a b)
  --simplify ((*) (ExpFld 1.0) b) = simplify b
  --simplify ((*) a (ExpFld 1.0)) = simplify a
  simplify ((*) (ExpFld n) b) = if isOne(n) then simplify b
                                else fieldexp.(*) (ExpFld n) (simplify b)
  simplify ((*) a (ExpFld n)) = if isOne(n) then simplify a
                                else fieldexp.(*) (simplify a) (ExpFld n)
  simplify ((*) a b) = if a == b then
               Function "sqr" [simplify a] else fieldexp.(*) (simplify a) (simplify b)
  simplify ((/) (ExpFld a) (ExpFld b)) = ExpFld (Prelude.Interfaces.(/) a b)
--  simplify ((/) (ExpFld 1.0) b) = Function "inv" [simplify b]
--  simplify ((/) a (ExpFld 1.0)) = simplify a
  simplify ((/) (ExpFld n) b) = if isOne(n) then Function "inv" [simplify b]
                                else fieldexp.(/) (ExpFld n) (simplify b)
  simplify ((/) a (ExpFld n)) = if isOne(n) then simplify a
                                else fieldexp.(/) (simplify a) (ExpFld n)
  simplify ((/) a b) = if a == b then
               ExpFld 1.0 else fieldexp.(/) (simplify a) (simplify b)
  -- I want to do:
  --simplify (Function a b) = Function a (map simplify b)
  -- but this is not proved to be total so, for now, don't
  -- simpilfy inside function:
  simplify (Function a b) = Function a b
  simplify Undefined = Undefined
