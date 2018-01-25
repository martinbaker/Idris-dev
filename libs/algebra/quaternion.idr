

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

module quat

import public fieldExpression
import public Data.Vect -- from base package
import public Data.Matrix -- from contrib package

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
||| Quaternion consists of 4 Double numbers
||| representing one Real and 3 Imaginary axis.
||| The 3 Imaginary axis are proceeded by the i, j and k operators
record Quaternion r where
  constructor Quat
  w:r
  x:r
  y:r
  z:r

--data Quaternion r = Quat r r r r
-- constructors

||| construct imaginary i term
i: FieldIfce r => r -> Quaternion r
i x = Quat 0 x 0 0

||| construct imaginary j term
j: FieldIfce r => r -> Quaternion r
j y = Quat 0 0 y 0

||| construct imaginary k term
k: FieldIfce r => r -> Quaternion r
k z = Quat 0 0 0 z

{-
-- deconstructors

||| real dimention
real : Quaternion r -> r
real (Quat w x y z) = w

||| imaginary dimention x
imagX : Quaternion r -> r
imagX (Quat w x y z) = x

||| imaginary dimention y
imagY : Quaternion r -> r
imagY (Quat w x y z) = y

||| imaginary dimention z
imagZ : Quaternion r -> r
imagZ (Quat w x y z) = z
-}
-- arithmatic

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

  ||| additive inverse
  negate : FieldIfce r => Quaternion r -> Quaternion r
  negate (Quat w1 x1 y1 z1) = 
    Quat (-w1) (-x1) (-y1) (-z1)

  ||| inverse of q, that is: 1/q
  inv : FieldIfce r => Quaternion r -> Quaternion r
  inv (Quat w1 x1 y1 z1) = 
    let denom = w1*w1+x1*x1+y1*y1+z1*z1 in
      Quat (w1/denom) (-x1/denom) (-y1/denom) (-z1/denom)

  ||| length of quaternion
  magnitude : FieldIfce r => Quaternion r -> r
  magnitude (Quat w1 x1 y1 z1) = sqrt(w1*w1+x1*x1+y1*y1+z1*z1)

  ||| make quaternion unit length
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/functions/
  normalise : FieldIfce r => Quaternion r -> Quaternion r
  normalise (Quat w1 x1 y1 z1)=
       let a = (Quat w1 x1 y1 z1) in
         Quat (w1/(magnitude a)) (x1/(magnitude a)) (y1/(magnitude a)) (z1/(magnitude a))

  ||| When representing rotations in 3D space (not spinors) then
  ||| negating every term does not change rotation represented so it
  ||| makes things more consistent to choose a prefered polariry for real term.
  ||| More information here:
  ||| http://www.euclideanspace.com/maths/algebra/realNormedAlgebra/quaternions/functions/
  ||| called when w==0 so make x positive
  makeZPositive : FieldIfce r => Quaternion r -> Quaternion r

  makeZPositive q =
    if (z q) < Zro then -q else q

  makeYPositive : FieldIfce r => Quaternion r -> Quaternion r

  makeYPositive q =
    case specialDouble (y q) of
      DZero _ _ => makeZPositive q
      DOne _ _ => if (y q) < Zro then -q else q
      DOther _ _ => if (y q) < Zro then -q else q

  makeXPositive : FieldIfce r => Quaternion r -> Quaternion r

  makeXPositive q =
    case specialDouble (x q) of
      DZero _ _ => makeYPositive q
      DOne _ _ => if (x q) < Zro then -q else q
      DOther _ _ => if (x q) < Zro then -q else q

  makeWPositive : FieldIfce r => Quaternion r -> Quaternion r

  makeWPositive q =
    case specialDouble (w q) of
      DZero _ _ => (makeXPositive q)
      DOne _ _ => if (w q) < Zro then -q else q
      DOther _ _ => if (w q) < Zro then -q else q

  ||| divide Quaternions
  ||| a / b = a * conj b * 1/(w2*w2 + x2*x2 + y2*y2 + z2*z2)
  (/) : FieldIfce r => Quaternion r -> Quaternion r -> Quaternion r
  (/) a b = a * inv(b)

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

||| I would like quaternions to be output (even in REPL) using
||| usual mathematical notation. Like this: 1.0 + i 2.0 - j 3.0 - k 4.0
implementation Show (Quaternion Double) where
{-  show (Quat 0.0 0.0 0.0 0.0) = "0"
  show (Quat w 0.0 0.0 0.0) = show w
  show (Quat 0.0 x 0.0 0.0) = (showHelper "i" x)
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val
  show (Quat 0.0 0.0 y 0.0) = (showHelper "j" y)
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val
  show (Quat 0.0 0.0 0.0 z) = (showHelper "k" z)
  where
    showHelper : FieldIfce Double => String -> Double -> String
    showHelper op val = if val < 0.0 then "-" ++ op ++ show (abs val) else "+" ++ op ++ show val -}
  show (Quat w x y z) = "(" ++ show w ++ (showHelper "i" x) ++ (showHelper "j" y) ++ (showHelper "k" z) ++ ")"
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

-- from contrib.Data.Matrix
--||| Matrix with n rows and m columns
--Matrix : Nat -> Nat -> Type -> Type
--Matrix n m a = Vect n (Vect m a)

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
            s:r = (sqrt(m00 + m11 + m22 + 1))*2 in
            Quat (s/4) ((m21-m12)/s) ((m02-m20)/s) ((m10-m01)/s)
        else
          if ((m00 > m11) && (m00 > m22))
          then
            let
              s:r = (sqrt(m00 - m11 - m22 + 1))*2 in
              Quat ((m21-m12)/s) (s/4) ((m10+m01)/s) ((m02+m20)/s)
          else
            if (m11 > m22)
            then
              let
                s:r = (sqrt(-m00 + m11 - m22 + 1))*2 in
                Quat ((m02-m20)/s) ((m10+m01)/s) (s/4) ((m21+m12)/s)
            else
              let
                s:r = (sqrt(-m00 - m11 + m22 + 1))*2 in
                Quat ((m10-m01)/s) ((m02+m20)/s) ((m21+m12)/s) (s/4)
  in (makeWPositive res)

||| Convert a quaternion representation of 3D rotation to a matrix
||| For more information about this subject see:
||| http://www.euclideanspace.com/maths/geometry/rotations/conversions/quaternionToMatrix/
quaternion2Matrix : FieldIfce r => Quaternion r -> Matrix 3 3 r
quaternion2Matrix (Quat w x1 y z) =
  let
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

