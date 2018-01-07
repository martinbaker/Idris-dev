{-
  (c) 2018 Copyright Martin Baker
  I would prefer GPL3 licence but if there were any interest in including
  this with Idris library then a compatible licence would be acceptable.
  
  This code attempts to implement quaternions using Idris.
  For an explanation with example session see this page:
  http://www.euclideanspace.com/prog/idris/quaternion/
  for more general information about objectives see this page:
  http://www.euclideanspace.com/prog/idris/
-}

module quatTerm

import public fieldExpressionTerm
import public Data.Vect -- uses base package
import public Data.Matrix -- uses contrib package

%access public export

{- In most cases Quaternion will be defined over Reals (In computer terms
  floating point - Double), an important application is to calculate finite
  rotations in 3 dimentional space.
  However, mathematically it can be defined over rings (such as Integers) so
  a more general data definition would be:
  data Quaternion Neg => a = Quat a a a a
  This would make definition more compatible with Data.Complex
  
  I am tempted to define the quaternion like this:
  data Quaternion r = Quat r r r r
  as it looks more efficient (but perhaps I'm still thinking in
  a Java style). The following seems more like Idris style?
  data Quaternion r= RealAxis r | I r | J r | K r | (++) (Quaternion r) (Quaternion r) 
-}

--data RealTerm r = R r
--data ITerm r = I r
--data JTerm r = J r
--data KTerm r = K r

data QTerm r = R r | I r | J r | K r

||| Quaternion consists of 4 Double numbers
||| representing one Real and 3 Imaginary axis.
||| The 3 Imaginary axis are proceeded by the i, j and k operators
data Quaternion r = Quat (QTerm r) (QTerm r) (QTerm r) (QTerm r)

-- constructors
{-
||| construct imaginary i term
i: FieldIfce r => r -> Quaternion r
i x = Quat 0 x 0 0

||| construct imaginary j term
j: FieldIfce r => r -> Quaternion r
j y = Quat 0 0 y 0

||| construct imaginary k term
k: FieldIfce r => r -> Quaternion r
k z = Quat 0 0 0 z
-}
-- deconstructors

||| real dimention
real : Quaternion r -> QTerm r
real (Quat w x y z) = w

||| imaginary dimention x
imagX : Quaternion r -> QTerm r
imagX (Quat w x y z) = x

||| imaginary dimention y
imagY : Quaternion r -> QTerm r
imagY (Quat w x y z) = y

||| imaginary dimention z
imagZ : Quaternion r -> QTerm r
imagZ (Quat w x y z) = z

scalar : QTerm r -> r
scalar (R a) = a
scalar (I a) = a
scalar (J a) = a
scalar (K a) = a

-- arithmatic
namespace addOps
  (+) : FieldIfce r => QTerm r -> QTerm r -> Quaternion r
  (+) (R a) (R b) = Quat (R (a+b)) (I Zro) (J Zro) (K Zro)
  (+) (R a) (I b) = Quat (R a) (I b) (J Zro) (K Zro)
  (+) (R a) (J b) = Quat (R a) (I Zro) (J b) (K Zro)
  (+) (R a) (K b) = Quat (R a) (I Zro) (J Zro) (K b)
  (+) (I a) (R b) = Quat (R b) (I a) (J Zro) (K Zro)
  (+) (I a) (I b) = Quat (R Zro) (I (a+b)) (J Zro) (K Zro)
  (+) (I a) (J b) = Quat (R Zro) (I a) (J b) (K Zro)
  (+) (I a) (K b) = Quat (R Zro) (I a) (J Zro) (K b)
  (+) (J a) (R b) = Quat (R b) (I Zro) (J a) (K Zro)
  (+) (J a) (I b) = Quat (R Zro) (I b) (J a) (K Zro)
  (+) (J a) (J b) = Quat (R Zro) (I Zro) (J (a+b)) (K Zro)
  (+) (J a) (K b) = Quat (R Zro) (I Zro) (J a) (K b)
  (+) (K a) (R b) = Quat (R b) (I Zro) (J Zro) (K a)
  (+) (K a) (I b) = Quat (R Zro) (I b) (J Zro) (K a)
  (+) (K a) (J b) = Quat (R Zro) (I Zro) (J b) (K a)
  (+) (K a) (K b) = Quat (R Zro) (I Zro) (J Zro) (K (a+b))

namespace termOps
  (+) : FieldIfce r => QTerm r -> QTerm r -> QTerm r
  (+) (R a) (R b) = R (a+b)
  (+) (I a) (I b) = I (a+b)
  (+) (J a) (J b) = J (a+b)
  (+) (K a) (K b) = K (a+b)

  (-) : FieldIfce r => QTerm r -> QTerm r -> QTerm r
  (-) (R a) (R b) = R (a-b)
  (-) (I a) (I b) = I (a-b)
  (-) (J a) (J b) = J (a-b)
  (-) (K a) (K b) = K (a-b)

  negate : FieldIfce r => QTerm r -> QTerm r
  negate (R a) = R (-a)
  negate (I a) = I (-a)
  negate (J a) = J (-a)
  negate (K a) = K (-a)

  (*) : FieldIfce r => QTerm r -> QTerm r -> QTerm r
  (*) (R a) (R b) = R (a*b)
  (*) (R a) (I b) = I (a*b)
  (*) (R a) (J b) = J (a*b)
  (*) (R a) (K b) = K (a*b)
  (*) (I a) (R b) = I (a*b)
  (*) (I a) (I b) = R (-(a*b))
  (*) (I a) (J b) = K (a*b)
  (*) (I a) (K b) = J (-(a*b))
  (*) (J a) (R b) = J (a*b)
  (*) (J a) (I b) = K (-(a*b))
  (*) (J a) (J b) = R (-(a*b))
  (*) (J a) (K b) = I (a*b)
  (*) (K a) (R b) = K (a*b)
  (*) (K a) (I b) = J (-(a*b))
  (*) (K a) (J b) = I (-(a*b))
  (*) (K a) (K b) = R (-(a*b))

  (/) : FieldIfce r => QTerm r -> QTerm r -> QTerm r
  (/) (R a) (R b) = R (a/b)
  (/) (R a) (I b) = I (a/b)
  (/) (R a) (J b) = J (a/b)
  (/) (R a) (K b) = K (a/b)
  (/) (I a) (R b) = I (a/b)
  (/) (I a) (I b) = R (a/b)
  (/) (I a) (J b) = K (-(a/b))
  (/) (I a) (K b) = J (a/b)
  (/) (J a) (R b) = J (a/b)
  (/) (J a) (I b) = K (a/b)
  (/) (J a) (J b) = R (a/b)
  (/) (J a) (K b) = I (-(a/b))
  (/) (K a) (R b) = K (a/b)
  (/) (K a) (I b) = J (a/b)
  (/) (K a) (J b) = I (a/b)
  (/) (K a) (K b) = R (a/b)

  sqrt : FieldIfce r => QTerm r -> QTerm r
  sqrt (R a) = R (sqrt a)

--  ifThenElse : Bool -> Lazy (QTerm r) -> Lazy (QTerm r) -> QTerm r
--  ifThenElse True  t e = t
--  ifThenElse False t e = e

ifThenElse : Bool -> Lazy (Quaternion r) -> Lazy (Quaternion r) -> Quaternion r
ifThenElse True  t e = t
ifThenElse False t e = e

namespace quatOps
  ||| add Quaternions by adding corresponding terms
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/arithmetic/
  (+) : FieldIfce r => Quaternion r -> Quaternion r -> Quaternion r
  (+) (Quat w1 x1 y1 z1) (Quat w2 x2 y2 z2) = Quat (w1+w2) (x1+x2) (y1+y2) (z1+z2)
  

  ||| subtract Quaternions by subtracting corresponding terms
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/arithmetic/
  (-) : FieldIfce r => Quaternion r -> Quaternion r -> Quaternion r
  (-) (Quat w1 x1 y1 z1) (Quat w2 x2 y2 z2) = Quat (w1-w2) (x1-x2) (y1-y2) (z1-z2)

  ||| multiply Quaternions
  ||| multiply not commutative
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/arithmetic/
  (*) : FieldIfce r => Quaternion r -> Quaternion r -> Quaternion r
  (*) (Quat w1 x1 y1 z1) (Quat w2 x2 y2 z2) =
    Quat (w1*w2 - x1*x2 - y1*y2 - z1*z2)
         (w1*x2 + x1*w2 + y1*z2 - z1*y2)
         (w1*y2 - x1*z2 + y1*w2 + z1*x2)
         (w1*z2 + x1*y2 - y1*x2 + z1*w2)

  ||| conjugate, negate imaginary terms, has useful properties
  ||| q * conj q = real number
  ||| conj a * conj b = conj (b * a)
  ||| also, if normalised, and q represents a rotation
  ||| then conj q represents the inverse ot that rotation.
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/functions/
  conj : FieldIfce r => Quaternion r -> Quaternion r
  conj (Quat w1 x1 y1 z1) = Quat (w1) (-x1) (-y1) (-z1)

  ||| inverse of q, that is: 1/q
  inv : FieldIfce r => Quaternion r -> Quaternion r
  inv (Quat w1 x1 y1 z1) = 
    let denom = w1*w1+x1*x1+y1*y1+z1*z1 in
      Quat (w1/denom) (-x1/denom) (-y1/denom) (-z1/denom)
  
  ||| length of quaternion
  magnitude : FieldIfce r => Quaternion r -> QTerm r
  magnitude (Quat w1 x1 y1 z1) = sqrt(w1*w1+x1*x1+y1*y1+z1*z1)

  ||| make quaternion unit length
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/functions/
  normalise : FieldIfce r => Quaternion r -> Quaternion r
  normalise (Quat w1 x1 y1 z1)=
       let a = (Quat w1 x1 y1 z1) in
         Quat (w1/(magnitude a)) (x1/(magnitude a)) (y1/(magnitude a)) (z1/(magnitude a))

  ||| divide Quaternions
  ||| a / b = a * conj b * 1/(w2*w2 + x2*x2 + y2*y2 + z2*z2)
  (/) : FieldIfce r => Quaternion r -> Quaternion r -> Quaternion r
  (/) a b = a * inv(b)

{-
-- scalar arithmatic
-- Put in different namespaces so we can overload arithmetic operations
namespace scalarOpsLeft
  ||| add to real term
  (+) : FieldIfce r => r -> Quaternion r -> Quaternion r
  (+) w1 (Quat w2 x2 y2 z2) = Quat (w1+w2) x2 y2 z2

  ||| subtract Quaternions by subtracting corresponding terms
  (-) : FieldIfce r => r -> Quaternion r -> Quaternion r
  (-) w1 (Quat w2 x2 y2 z2) = Quat (w1-w2) (-x2) (-y2) (-z2)

  ||| multiply by real term
  (*) : FieldIfce r => r -> Quaternion r -> Quaternion r
  (*) w1 (Quat w2 x2 y2 z2) = Quat (w1*w2) (w1*x2) (w1*y2) (w1*z2)

namespace scalarOpsRight
  ||| add to real term
  (+) : FieldIfce r => Quaternion r -> r -> Quaternion r
  (+) (Quat w1 x1 y1 z1) w2 = Quat (w1+w2) x1 y1 z1
  
  ||| subtract Quaternions by subtracting corresponding terms
  (-) : FieldIfce r => Quaternion r -> r -> Quaternion r
  (-) (Quat w1 x1 y1 z1) w2 = Quat (w1-w2) x1 y1 z1

  ||| multiply by real term
  (*) : FieldIfce r => Quaternion r -> r -> Quaternion r
  (*) (Quat w1 x1 y1 z1) w2 = Quat (w1*w2) (x1*w2) (y1*w2) (z1*w2)
-}
||| I would like quaternions to be output (even in REPL) using
||| usual mathematical notation. Like this: 1.0 + i 2.0 - j 3.0 - k 4.0
implementation Show (Quaternion Double) where
  show (Quat (R 0.0) (I 0.0) (J 0.0) (K 0.0)) = "0"
  show (Quat (R w) (I 0.0) (J 0.0) (K 0.0)) = show w
  show (Quat (R 0.0) (I x) (J 0.0) (K 0.0)) = (showHelper "i" x)
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val
  show (Quat (R 0.0) (I 0.0) (J y) (K 0.0)) = (showHelper "j" y)
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val
  show (Quat (R 0.0) (I 0.0) (J 0.0) (K z)) = (showHelper "k" z)
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val
  show (Quat (R w) (I x) (J y) (K z)) = "(" ++ show w ++ (showHelper "i" x) ++ (showHelper "j" y) ++ (showHelper "k" z) ++ ")"
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val


-- Should I use showPrec instead of show to only put parenthasis around quaternion when needed?
-- Parenthasis is only needed if quaternion is multiplied or divided by something.
--    showPrec p (Quat w x y z) = showParens (p >= plus_i) $ showPrec plus_i w ++ " +i " ++ showPrec plus_i x
--      where plus_i : Prec
--            plus_i = User 6

{-
  Application - Finite Rotations in 3D Space
  
  See this web page for more information.
  http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/transforms/
  
  In order to represent finite rotations in 3D space and use them to
  compose rotations and to do varous calculations we have different options.
  We could represent a rotation as a 3x3 matrix or we could represent it as
  a quaternion (normalised to unit length).
  
  Each of these has pros and cons. The advantage of quaternions are:
  * It is easier to interpolate between 2 orientations.
  * It is easier to normalise.
  * It only requires 4 Double values instead of 9.
  
  Is there any way to use the Idris type system to ensure the quaternion is
  always normalised to unit length? I don't think so because floating point
  errors can always cause small deviations from unit length.
  
  Since both quaternions and matricies have advantages they are both used in
  various rendering libraries and games engines. It is useful to be
  able to translate between them using the following functions:
-}

{- matrix2Quaternion - Even though matrix2Quaternion contains division and square
root it should still be total because we switch to different functions to avoid
singularities. I guess that may be hard to prove using type system!
-}
||| Convert a matrix representation of 3D rotation to quaternion
||| For more information about this subject see:
||| http://www.euclideanspace.com/maths/geometry/rotations/conversions/matrixToQuaternion/
matrix2Quaternion : FieldIfce r => Matrix 3 3 r -> Quaternion r
matrix2Quaternion m =
  let m0:Vect 3 r = index 0 m
      m1:Vect 3 r = index 1 m
      m2:Vect 3 r = index 2 m
      m00:r = index 0 m0
      m11:r = index 1 m1
      m22:r = index 2 m2
      trace:r = m00 + m11 + m22
      m01:r = index 1 m0
      m02:r = index 2 m0
      m10:r = index 0 m1
      m12:r = index 2 m1
      m20:r = index 0 m2
      m21:r = index 1 m2
      res:Quaternion r =
        if (trace > Zro)
        then
          let
            s:QTerm r = R ((sqrt(m00 + m11 + m22 + 1))*(One+One)) in
            Quat (s/(R 4)) (I (m21-m12)/s) (J (m02-m20)/s) (K (m10-m01)/s)
        else
          if ((m00 > m11) && (m00 > m22))
          then
            let
              s:QTerm r = R ((sqrt(m00 - m11 - m22 + 1))*(One+One)) in
              Quat (R (m21-m12)/s) ((I 1)*s/(R 4)) (J (m10+m01)/s) (K (m02+m20)/s)
          else
            if (m11 > m22)
            then
              let
                s:QTerm r = R ((sqrt(-m00 + m11 - m22 + 1))*(One+One)) in
                Quat (R (m02-m20)/s) (I (m10+m01)/s) ((J 1)*s/(R 4)) (K (m21+m12)/s)
            else
              let
                s:QTerm r = R ((sqrt(-m00 - m11 + m22 + 1))*(One+One)) in
                Quat (R (m10-m01)/s) (I (m02+m20)/s) (J (m21+m12)/s) ((K 1)*s/(R 4))
  in res

||| Convert a quaternion representation of 3D rotation to a matrix
||| For more information about this subject see:
||| http://www.euclideanspace.com/maths/geometry/rotations/conversions/quaternionToMatrix/
quaternion2Matrix : FieldIfce r => Quaternion r -> Matrix 3 3 r
quaternion2Matrix (Quat ww xx yy zz) =
  let
    w:r = scalar ww
    x1:r = scalar xx
    y:r = scalar yy
    z:r = scalar zz
    xx:r = x1 * x1
    xy:r = x1 * y
    xz:r = x1 * z
    xw:r = x1 * w
    yy:r = y * y
    yz:r = y * z
    yw:r = y * w
    zz:r = z * z
    zw:r = z * w
    m00:r = 1 - 2 * ( yy + zz )
    m01:r =     2 * ( xy - zw )
    m02:r =     2 * ( xz + yw )
    m10:r =     2 * ( xy + zw )
    m11:r = 1 - 2 * ( xx + zz )
    m12:r =     2 * ( yz - xw )
    m20:r =     2 * ( xz - yw )
    m21:r =     2 * ( yz + xw )
    m22:r = 1 - 2 * ( xx + yy )
    m0:Vect 3 r = m00 :: m01 :: m02 :: Vect.Nil
    m1:Vect 3 r = m10 :: m11 :: m12 :: Vect.Nil
    m2:Vect 3 r = m20 :: m21 :: m22 :: Vect.Nil
    m:Vect 3 (Vect 3 r) = m0 :: m1 :: m2 :: Vect.Nil
      in m

