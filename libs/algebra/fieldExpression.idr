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

||| We need to treat 0.0 and 1.0 differently from other
||| floating point values. For instance we want to simplify
||| x+0.0 to x and we need to avoid 0.0 in divisor. We therefore
||| have this view type which can match on particular Double values
data SpecialDouble : (ty:Type) -> (x:ty) -> Type where
  DZero: (ty:Type) -> (x:ty) -> SpecialDouble ty x
  DOne: (ty:Type) -> (x:ty) -> SpecialDouble ty x
  DOther: (ty:Type) -> (x:ty) -> SpecialDouble ty x

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
  negate x = Function "negate" [x]
  (-) a b = a - b

Fractional ExpressionField where
  (/) a b = a / b
  recip x = (ExpFld 1.0) / x

-- Would like:
--interface (Neg ty, Fractional ty, Ord ty, Show ty) => FieldIfce ty where
-- but: Can't find implementation for Show ExpressionField
||| Define the mathematical structures over a field.
||| Not just Float or Double but also variables (to implement
||| algebra).
interface (Neg ty, Fractional ty, Ord ty) => FieldIfce ty where
  (==) : ty -> ty -> Bool
  sqrt : ty -> ty
  Zro : ty
  One : ty
  isZro : ty -> Bool
  isOne : ty -> Bool
  ifThenElse : Bool -> Lazy ty -> Lazy ty -> ty
  show : ty -> String
  simplify : ty -> ty
  evaluate : ty -> String -> ty
  ||| Covering function for SpecialDouble
  specialDouble : (v:ty) -> SpecialDouble ty v
    
||| Implementation of FieldIfce over Double
||| Use this when we just need a numerical result without
||| any variables.
FieldIfce Double where
  (==) = boolOp prim__eqFloat
  sqrt x = prim__floatSqrt x
  Zro = 0.0
  One = 1.0
  isZro x = boolOp prim__eqFloat x 0.0
  isOne x = boolOp prim__eqFloat x 1.0
  ifThenElse True  t e = t
  ifThenElse False t e = e
  show a = prim__floatToStr a
  simplify a = a
  evaluate a b = a
  specialDouble v = if isZro v then DZero Double v else
                    if isOne v then DOne Double v else
                      DOther Double v


||| Implementation of FieldIfce over ExpressionField
||| which contains variables in addition to functions and numbers.
FieldIfce ExpressionField where
  (==) a b = False
  sqrt x = Function "sqrt" [x]
  Zro = ExpFld 0.0
  One = ExpFld 1.0
  isZro (ExpFld 0.0) = True
  isZro _ = False
  isOne (ExpFld 1.0) = True
  isOne _ = False
  ifThenElse True  t e = Undefined
  ifThenElse False t e = Undefined
  show (ExpFld a) = prim__floatToStr a
  show (Var a) = a
  show ((+) a b) = (show a) ++ "+" ++ (show b)
  show ((-) a b) = (show a) ++ "-" ++ (show b)
  show ((*) a b) = (show a) ++ "*" ++ (show b)
  show ((/) a b) = (show a) ++ "/" ++ (show b)
  show (Function a b) = (show a) ++ "("  -- ++ (show b) ++ ")"
  show Undefined = " undefined "
  evaluate a b = a
  specialDouble v = if isZro v then DZero ExpressionField v else
                    if isOne v then DOne ExpressionField v else
                      DOther ExpressionField v
  simplify s =
    s
{-    let res : ExpressionField = s
       lastpass : ExpressionField = s
       level : Nat = 0
       loopBreaker : Nat = 0
       while loopBreaker < 10000 repeat
           loopBreaker := loopBreaker + 1
           if level=0 then res := TTRemoveEmpty(res, trace)
           if level=1 then res := TTRemoveZero(res, trace)
           if level=2 then res := TTRemoveGeneratorIfIdentity(res, trace)
           if level=3 then res := TTRenameGenerator(res, trace)
           if level=4 then res := TTRemoveEleTimesInverse(res, trace)
           if level=5 then res := TTRemoveDuplicateRelation(res, trace)
           if level=6 then res := TTSubstitute(res, trace)
           if level=7 then return TTMinimiseInverses(res, trace)
           if isSimpler?(res, lastpass)
               then level := 0
               else level := level + 1
           lastpass := res
  in res
-}

{-
||| We need to treat 0.0 and 1.0 differently from other
||| floating point values. For instance we want to simplify
||| x+0.0 to x and we need to avoid 0.0 in divisor. We therefore
||| have this view type which can match on particular Double values
data SpecialDouble : FieldIfce r => r -> Type where
  DZero: FieldIfce r => (x:r) -> SpecialDouble x
  DOne: FieldIfce r => (x:r) -> SpecialDouble x
  DOther: FieldIfce r => (x:r) -> SpecialDouble x

-- Must be called with parameter of type Double or ExpressionField
-- otherwise we get error: Can't find
-- implementation for FieldIfce (Quaternion Double)
||| Covering function for SpecialDouble
specialDouble : FieldIfce r => (v:r) -> SpecialDouble v
specialDouble v = if isZro v then DZero v else
                    if isOne v then DOne v else
                      DOther v
-}

