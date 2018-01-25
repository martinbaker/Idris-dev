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

module testQuat

-- Local Variables:
-- idris-load-packages: ("algebra")
-- End:
import public fieldExpression
import public quaternion
--import public Data.Vect

%access export

infix 6 ~~

||| The CloseEnough interface defines 'close enough'.
||| Due to floating point errors we cant check for equality so
||| check if it near enough.
interface CloseEnough ty where
  (~~) : ty -> ty -> Bool

||| Close Enough for Doubles
CloseEnough Double where
  --(~~) 0.0 0.0 = True -- causes runtime error Can't match on (0.0)
  --(~~) a (-a) = False
  (~~) a b =
    let denom = abs(a+b)
    in if denom < 0.001
       then (abs a) < 0.001
       else (abs(a-b)/denom) < 0.001

||| Close Enough for Quaternion
CloseEnough (Quaternion Double) where
  (~~) (Quat aw ax ay az) (Quat bw bx by bz) =
    (aw ~~ bw) && (ax ~~ bx) && (ay ~~ by) && (az ~~ bz)

implementation (CloseEnough ty) => CloseEnough (Vect len ty) where
  (~~) []      []      = True
  (~~) (x::xs) (y::ys) = x ~~ y && xs ~~ ys

assertCloseEnough : CloseEnough a => (given : a) -> (expected : a) -> IO ()
assertCloseEnough g e = if g ~~ e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

seperateTests1 : IO ()
seperateTests1 = putStrLn "simplify expression tests:"

seperateTests2 : IO ()
seperateTests2 = putStrLn "quaternion arithmatic tests:"

seperateTests3 : IO ()
seperateTests3 = putStrLn "rotation quaternion to matrix tests:"

seperateTests4 : IO ()
seperateTests4 = putStrLn "rotation matrix to quaternion tests:"

seperateTests5 : IO ()
seperateTests5 = putStrLn "simplify expression tests:"

||| test simplify expression
||| 1+2=3
testExpressionSimplify1 : IO()
testExpressionSimplify1 = 
  let e1 = ExpFld 1.0
      e2 = ExpFld 2.0
      e3 = ExpFld 3.0   
  in assertEq e3 (simplify (fieldexp.(+) e1 e2))

||| test simplify expression
||| 1-2=-1
testExpressionSimplify2 : IO()
testExpressionSimplify2 = 
  let e1 = ExpFld 1.0
      e2 = ExpFld 2.0
      e3 = ExpFld (-1.0)
  in assertEq e3 (simplify (fieldexp.(-) e1 e2))

||| test simplify expression
||| 2*3=6
testExpressionSimplify3 : IO()
testExpressionSimplify3 = 
  let e1 = ExpFld 2.0
      e2 = ExpFld 3.0
      e3 = ExpFld 6.0   
  in assertEq e3 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| 6/3=2
testExpressionSimplify4 : IO()
testExpressionSimplify4 = 
  let e1 = ExpFld 6.0
      e2 = ExpFld 3.0
      e3 = ExpFld 2.0   
  in assertEq e3 (simplify (fieldexp.(/) e1 e2))

||| test simplify expression
||| 0+x=x
testExpressionSimplify5 : IO()
testExpressionSimplify5 = 
  let e1 = ExpFld 0.0
      e2 = Var "x"   
  in assertEq e2 (simplify (fieldexp.(+) e1 e2))

||| test simplify expression
||| x+0=x
testExpressionSimplify6 : IO()
testExpressionSimplify6 = 
  let e1 = Var "x"
      e2 = ExpFld 0.0  
  in assertEq e1 (simplify (fieldexp.(+) e1 e2))

||| test simplify expression
||| x-0=x
testExpressionSimplify7 : IO()
testExpressionSimplify7 = 
  let e1 = Var "x"
      e2 = ExpFld 0.0  
  in assertEq e1 (simplify (fieldexp.(-) e1 e2))

||| test simplify expression
||| 0-x=-x
testExpressionSimplify8 : IO()
testExpressionSimplify8 = 
  let e1 = ExpFld 0.0
      e2 = Var "x"
      e3 = Function "negate" [e2]  
  in assertEq e3 (simplify (fieldexp.(-) e1 e2))

||| test simplify expression
||| x*1=x
testExpressionSimplify9 : IO()
testExpressionSimplify9 = 
  let e1 = Var "x"
      e2 = ExpFld 1.0  
  in assertEq e1 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| 1*x=x
testExpressionSimplify10 : IO()
testExpressionSimplify10 = 
  let e1 = ExpFld 1.0
      e2 = Var "x"   
  in assertEq e2 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| x/1=x
testExpressionSimplify11 : IO()
testExpressionSimplify11 = 
  let e1 = Var "x"
      e2 = ExpFld 1.0  
  in assertEq e1 (simplify (fieldexp.(/) e1 e2))

||| test simplify expression
||| 1/x=inv x
testExpressionSimplify12 : IO()
testExpressionSimplify12 = 
  let e1 = ExpFld 1.0
      e2 = Var "x"
      e3 = Function "inv" [e2] 
  in assertEq e3 (simplify (fieldexp.(/) e1 e2))


||| test multipication - first axioms
||| i*i = j*j = k*k = i*j*k = -1
testQuaternion1 : IO()
testQuaternion1 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertCloseEnough qr (qi*qi)
 
testQuaternion2 : IO()
testQuaternion2 = 
  let qj=Quat 0.0 0.0 1.0 0.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertCloseEnough qr (qj*qj)

testQuaternion3 : IO()
testQuaternion3 = 
  let qk=Quat 0.0 0.0 1.0 0.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertCloseEnough qr (qk*qk)

testQuaternion4 : IO()
testQuaternion4 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertCloseEnough qr (qi*qj*qk)

||| testQuaternion multipication - multiplcation by reals
testQuaternion5 : IO()
testQuaternion5 = 
  let qr=Quat 1.0 0.0 0.0 0.0
  in assertCloseEnough qr (qr*qr)

testQuaternion6 : IO()
testQuaternion6 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qi=Quat 0.0 1.0 0.0 0.0
  in assertCloseEnough qi (qr*qi)
 
testQuaternion7 : IO()
testQuaternion7 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in assertCloseEnough qj (qr*qj)
 
testQuaternion8 : IO()
testQuaternion8 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough qk (qr*qk)
 
testQuaternion9 : IO()
testQuaternion9 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qi=Quat 0.0 1.0 0.0 0.0
  in assertCloseEnough qi (qi*qr)
 
testQuaternion10 : IO()
testQuaternion10 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in assertCloseEnough qj (qj*qr)
 
testQuaternion11 : IO()
testQuaternion11 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough qk (qk*qr)

||| testQuaternion multipication - multiplcation of different
||| imaginary axes anticommute
testQuaternion12 : IO()
testQuaternion12 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough qk (qi*qj)
 
testQuaternion13 : IO()
testQuaternion13 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough (-qk) (qj*qi)
 
testQuaternion14 : IO()
testQuaternion14 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough qi (qj*qk)
 
testQuaternion15 : IO()
testQuaternion15 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough (-qi) (qk*qj)
 
testQuaternion16 : IO()
testQuaternion16 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough (-qj) (qi*qk)
 
testQuaternion17 : IO()
testQuaternion17 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertCloseEnough qj (qk*qi)

||| testQuaternion addition
testQuaternion18 : IO()
testQuaternion18 = 
  let qa=Quat 1.0 2.0 3.0 4.0
      qb=Quat 1.0 1.0 1.0 1.0
      qres=Quat 2.0 3.0 4.0 5.0
  in assertCloseEnough qres (qa+qb)

||| testQuaternion subtract
testQuaternion19 : IO()
testQuaternion19 = 
  let qa=Quat 1.0 2.0 3.0 4.0
      qb=Quat 1.0 1.0 1.0 1.0 
      qres=Quat 0.0 1.0 2.0 3.0
  in assertCloseEnough qres (qa-qb)

||| test conversion between 3D rotation representations
||| using quaternions or 3x3 matrix.
testRotate00 : IO()
testRotate00 = 
  let q=Quat 1.0 0.0 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 1, 0], [0, 0, 1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate01 : IO()
testRotate01 = 
  let q=Quat 0.7071 0.0 0.7071 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, 1, 0], [-1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate02 : IO()
testRotate02 = 
  let q=Quat 0.0 0.0 1.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 1, 0], [0, 0, -1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate03 : IO()
testRotate03 = 
  let q=Quat 0.7071 0.0 (-0.7071) 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, 1, 0], [1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate10 : IO()
testRotate10 = 
  let q=Quat 0.7071 0.0 0.0 0.7071
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [1, 0, 0], [0, 0, 1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate11 : IO()
testRotate11 = 
  let q=Quat 0.5 0.5 0.5 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [1, 0, 0], [0, 1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate12 : IO()
testRotate12 = 
  let q=Quat 0.0 0.7071 0.7071 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [1, 0, 0], [0, 0, -1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate13 : IO()
testRotate13 = 
  let q=Quat 0.5 (-0.5) (-0.5) 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [1, 0, 0], [0, -1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate20 : IO()
testRotate20 = 
  let q=Quat 0.7071 0.0 0.0 (-0.7071)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [-1, 0, 0], [0, 0, 1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate21 : IO()
testRotate21 = 
  let q=Quat 0.5 (-0.5) 0.5 (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [-1, 0, 0], [0, -1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate22 : IO()
testRotate22 = 
  let q=Quat 0.0 (-0.7071) 0.7071 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [-1, 0, 0], [0, 0,-1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate23 : IO()
testRotate23 = 
  let q=Quat 0.5 0.5 (-0.5) (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [-1, 0, 0], [0, 1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate30 : IO()
testRotate30 = 
  let q=Quat 0.7071 0.7071 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, -1], [0, 1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate31 : IO()
testRotate31 = 
  let q=Quat 0.5 0.5 0.5 (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, -1], [-1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate32 : IO()
testRotate32 = 
  let q=Quat 0.0 0.0 0.7071 (-0.7071)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, -1], [0, -1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate33 : IO()
testRotate33 = 
  let q=Quat 0.5 0.5 (-0.5) 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, -1], [1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate40 : IO()
testRotate40 = 
  let q=Quat 0.0 1.0 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, -1, 0], [0, 0, -1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate41 : IO()
testRotate41 = 
  let q=Quat 0.0 0.7071 0.0 (-0.7071)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, -1, 0], [-1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate42 : IO()
testRotate42 = 
  let q=Quat 0.0 0.0 0.0 1.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, -1, 0], [0, 0, 1]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate43 : IO()
testRotate43 = 
  let q=Quat 0.0 0.7071 0.0 0.7071
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, -1, 0], [1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate50 : IO()
testRotate50 = 
  let q=Quat 0.7071 (-0.7071) 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, 1], [0, -1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate51 : IO()
testRotate51 = 
  let q=Quat 0.5 (-0.5) 0.5 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, 1], [-1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate52 : IO()
testRotate52 = 
  let q=Quat 0.0 0.0 0.7071 0.7071
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, 1], [0, 1, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

testRotate53 : IO()
testRotate53 = 
  let q=Quat 0.5 (-0.5) (-0.5) (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, 1], [1, 0, 0]]
  in assertCloseEnough m (quaternion2Matrix q)

||| now test conversion between 3D rotation in opposite direction 
||| from 3x3 matrix to quaternion.
testRotateM2Q00 : IO()
testRotateM2Q00 = 
  let q=Quat 1.0 0.0 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 1, 0], [0, 0, 1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q01 : IO()
testRotateM2Q01 = 
  let q=Quat 0.7071 0.0 0.7071 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, 1, 0], [-1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q02 : IO()
testRotateM2Q02 = 
  let q=Quat 0.0 0.0 1.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 1, 0], [0, 0, -1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q03 : IO()
testRotateM2Q03 = 
  let q=Quat 0.7071 0.0 (-0.7071) 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, 1, 0], [1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q10 : IO()
testRotateM2Q10 = 
  let q=Quat 0.7071 0.0 0.0 0.7071
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [1, 0, 0], [0, 0, 1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q11 : IO()
testRotateM2Q11 = 
  let q=Quat 0.5 0.5 0.5 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [1, 0, 0], [0, 1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q12 : IO()
testRotateM2Q12 = 
  let q=Quat 0.0 0.7071 0.7071 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [1, 0, 0], [0, 0, -1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q13 : IO()
testRotateM2Q13 = 
  let q=Quat 0.5 (-0.5) (-0.5) 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [1, 0, 0], [0, -1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q20 : IO()
testRotateM2Q20 = 
  let q=Quat 0.7071 0.0 0.0 (-0.7071)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [-1, 0, 0], [0, 0, 1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q21 : IO()
testRotateM2Q21 = 
  let q=Quat 0.5 (-0.5) 0.5 (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [-1, 0, 0], [0, -1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q22 : IO()
testRotateM2Q22 = 
  let q=Quat 0.0 0.7071 (-0.7071) 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [-1, 0, 0], [0, 0,-1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q23 : IO()
testRotateM2Q23 = 
  let q=Quat 0.5 0.5 (-0.5) (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [-1, 0, 0], [0, 1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q30 : IO()
testRotateM2Q30 = 
  let q=Quat 0.7071 0.7071 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, -1], [0, 1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q31 : IO()
testRotateM2Q31 = 
  let q=Quat 0.5 0.5 0.5 (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, -1], [-1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

||| I had to negate q because 'makeRealPositive' does not make
||| y term positive if w and x are zero
testRotateM2Q32 : IO()
testRotateM2Q32 = 
  let q=Quat 0.0 0.0 0.7071 (-0.7071)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, -1], [0, -1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q33 : IO()
testRotateM2Q33 = 
  let q=Quat 0.5 0.5 (-0.5) 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, -1], [1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q40 : IO()
testRotateM2Q40 = 
  let q=Quat 0.0 1.0 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, -1, 0], [0, 0, -1]]
  in assertCloseEnough q (matrix2Quaternion m)

||| I had to negate q because 'makeRealPositive' does not make
||| x term positive if w is zero
testRotateM2Q41 : IO()
testRotateM2Q41 = 
  let q=Quat 0.0 0.7071 0.0 (-0.7071)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, -1, 0], [-1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q42 : IO()
testRotateM2Q42 = 
  let q=Quat 0.0 0.0 0.0 1.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, -1, 0], [0, 0, 1]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q43 : IO()
testRotateM2Q43 = 
  let q=Quat 0.0 0.7071 0.0 0.7071
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, -1, 0], [1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q50 : IO()
testRotateM2Q50 = 
  let q=Quat 0.7071 (-0.7071) 0.0 0.0
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, 1], [0, -1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q51 : IO()
testRotateM2Q51 = 
  let q=Quat 0.5 (-0.5) 0.5 0.5
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, 1], [-1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q52 : IO()
testRotateM2Q52 = 
  let q=Quat 0.0 0.0 0.7071 0.7071
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, 1], [0, 1, 0]]
  in assertCloseEnough q (matrix2Quaternion m)

testRotateM2Q53 : IO()
testRotateM2Q53 = 
  let q=Quat 0.5 (-0.5) (-0.5) (-0.5)
      m:(CloseEnough Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, 1], [1, 0, 0]]
  in assertCloseEnough q (matrix2Quaternion m)
  --in putStrLn ("q ="++ show(matrix2Quaternion m))
