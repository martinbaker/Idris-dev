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
data ExpressionField = ExpFld Double
                    | Var String
                    | (+) ExpressionField ExpressionField
                    | (-) ExpressionField ExpressionField
                    | (*) ExpressionField ExpressionField
                    | (/) ExpressionField ExpressionField
                    | Function String (List ExpressionField)
                    | Undefined

||| No way to do this because we don't know value of variable
Eq ExpressionField where
  (==) _ _ = True

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
  --abs x = Function "abs" [x]
  negate x = Function "negate" [x]
  (-) a b = a - b

Fractional ExpressionField where
  (/) a b = a / b
  recip x = (ExpFld 1.0) / x

||| Define the mathematical structures over a field.
||| Not just Float or Double but also variables (to implement
||| algebra).
interface (Neg ty, Fractional ty, Ord ty) => FieldIfce ty where
    sqrt : ty -> ty
    Zro : ty
    One : ty
    ifThenElse : Bool -> Lazy ty -> Lazy ty -> ty
    
||| Implementation of FieldIfce over Double
||| Use this when we just need a numerical result without
||| any variables.
FieldIfce Double where
  sqrt x = prim__floatSqrt x
  Zro = 0.0
  One = 1.0
  ifThenElse True  t e = t
  ifThenElse False t e = e

||| Implementation of FieldIfce over ExpressionField
||| which contains variables in addition to functions and numbers.
FieldIfce ExpressionField where
    sqrt x = Function "sqrt" [x]
    Zro = ExpFld 0.0
    One = ExpFld 1.0
    ifThenElse True  t e = Undefined
    ifThenElse False t e = Undefined
