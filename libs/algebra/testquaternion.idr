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
import public quaternion
--import public Data.Vect

%access export

infix 6 ~~

||| The Close interface defines 'close enough'.
||| Due to floating point errors we cant check for equality so
||| check if it near enough.
interface Close ty where
  (~~) : ty -> ty -> Bool

||| Close Enough for Doubles
Close Double where
  --(~~) 0.0 0.0 = True -- causes runtime error Can't match on (0.0)
  --(~~) a (-a) = False
  (~~) a b =
    let denom = abs(a+b)
    in if denom < 0.001
       then (abs a) < 0.001
       else (abs(a-b)/denom) < 0.001

||| Close Enough for Quaternion
Close (Quaternion Double) where
  (~~) (Quat aw ax ay az) (Quat bw bx by bz) =
    (aw ~~ bw) && (ax ~~ bx) && (ay ~~ by) && (az ~~ bz)

implementation (Close ty) => Close (Vect len ty) where
  (~~) []      []      = True
  (~~) (x::xs) (y::ys) = x ~~ y && xs ~~ ys

assertClose : Close a => (given : a) -> (expected : a) -> IO ()
assertClose g e = if g ~~ e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

||| test multipication - first axioms
||| i*i = j*j = k*k = i*j*k = -1
test1 : IO()
test1 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertClose qr (qi*qi)
 
test2 : IO()
test2 = 
  let qj=Quat 0.0 0.0 1.0 0.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertClose qr (qj*qj)

test3 : IO()
test3 = 
  let qk=Quat 0.0 0.0 1.0 0.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertClose qr (qk*qk)

test4 : IO()
test4 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
      qr=Quat (-1) 0.0 0.0 0.0
  in assertClose qr (qi*qj*qk)

||| test multipication - multiplcation by reals
test5 : IO()
test5 = 
  let qr=Quat 1.0 0.0 0.0 0.0
  in assertClose qr (qr*qr)

test6 : IO()
test6 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qi=Quat 0.0 1.0 0.0 0.0
  in assertClose qi (qr*qi)
 
test7 : IO()
test7 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in assertClose qj (qr*qj)
 
test8 : IO()
test8 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose qk (qr*qk)
 
test9 : IO()
test9 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qi=Quat 0.0 1.0 0.0 0.0
  in assertClose qi (qi*qr)
 
test10 : IO()
test10 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in assertClose qj (qj*qr)
 
test11 : IO()
test11 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose qk (qk*qr)

||| test multipication - multiplcation of different
||| imaginary axes anticommute
test12 : IO()
test12 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose qk (qi*qj)
 
test13 : IO()
test13 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose (-qk) (qj*qi)
 
test14 : IO()
test14 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose qi (qj*qk)
 
test15 : IO()
test15 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose (-qi) (qk*qj)
 
test16 : IO()
test16 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose (-qj) (qi*qk)
 
test17 : IO()
test17 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in assertClose qj (qk*qi)

||| test addition
test18 : IO()
test18 = 
  let qa=Quat 1.0 2.0 3.0 4.0
      qb=Quat 1.0 1.0 1.0 1.0
      qres=Quat 2.0 3.0 4.0 5.0
  in assertClose qres (qa+qb)

||| test subtract
test19 : IO()
test19 = 
  let qa=Quat 1.0 2.0 3.0 4.0
      qb=Quat 1.0 1.0 1.0 1.0 
      qres=Quat 0.0 1.0 2.0 3.0
  in assertClose qres (qa-qb)

||| test conversion between 3D rotation representations
||| using quaternions or 3x3 matrix.
testRotate00 : IO()
testRotate00 = 
  let q=Quat 1.0 0.0 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 1, 0], [0, 0, 1]]
  in assertClose m (quaternion2Matrix q)

testRotate01 : IO()
testRotate01 = 
  let q=Quat 0.7071 0.0 0.7071 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, 1, 0], [-1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate02 : IO()
testRotate02 = 
  let q=Quat 0.0 0.0 1.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 1, 0], [0, 0, -1]]
  in assertClose m (quaternion2Matrix q)

testRotate03 : IO()
testRotate03 = 
  let q=Quat 0.7071 0.0 (-0.7071) 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, 1, 0], [1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate10 : IO()
testRotate10 = 
  let q=Quat 0.7071 0.0 0.0 0.7071
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [1, 0, 0], [0, 0, 1]]
  in assertClose m (quaternion2Matrix q)

testRotate11 : IO()
testRotate11 = 
  let q=Quat 0.5 0.5 0.5 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [1, 0, 0], [0, 1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate12 : IO()
testRotate12 = 
  let q=Quat 0.0 0.7071 0.7071 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [1, 0, 0], [0, 0, -1]]
  in assertClose m (quaternion2Matrix q)

testRotate13 : IO()
testRotate13 = 
  let q=Quat 0.5 (-0.5) (-0.5) 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [1, 0, 0], [0, -1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate20 : IO()
testRotate20 = 
  let q=Quat 0.7071 0.0 0.0 (-0.7071)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [-1, 0, 0], [0, 0, 1]]
  in assertClose m (quaternion2Matrix q)

testRotate21 : IO()
testRotate21 = 
  let q=Quat 0.5 (-0.5) 0.5 (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [-1, 0, 0], [0, -1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate22 : IO()
testRotate22 = 
  let q=Quat 0.0 (-0.7071) 0.7071 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [-1, 0, 0], [0, 0,-1]]
  in assertClose m (quaternion2Matrix q)

testRotate23 : IO()
testRotate23 = 
  let q=Quat 0.5 0.5 (-0.5) (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [-1, 0, 0], [0, 1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate30 : IO()
testRotate30 = 
  let q=Quat 0.7071 0.7071 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, -1], [0, 1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate31 : IO()
testRotate31 = 
  let q=Quat 0.5 0.5 0.5 (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, -1], [-1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate32 : IO()
testRotate32 = 
  let q=Quat 0.0 0.0 0.7071 (-0.7071)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, -1], [0, -1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate33 : IO()
testRotate33 = 
  let q=Quat 0.5 0.5 (-0.5) 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, -1], [1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate40 : IO()
testRotate40 = 
  let q=Quat 0.0 1.0 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, -1, 0], [0, 0, -1]]
  in assertClose m (quaternion2Matrix q)

testRotate41 : IO()
testRotate41 = 
  let q=Quat 0.0 0.7071 0.0 (-0.7071)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, -1, 0], [-1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate42 : IO()
testRotate42 = 
  let q=Quat 0.0 0.0 0.0 1.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, -1, 0], [0, 0, 1]]
  in assertClose m (quaternion2Matrix q)

testRotate43 : IO()
testRotate43 = 
  let q=Quat 0.0 0.7071 0.0 0.7071
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, -1, 0], [1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate50 : IO()
testRotate50 = 
  let q=Quat 0.7071 (-0.7071) 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, 1], [0, -1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate51 : IO()
testRotate51 = 
  let q=Quat 0.5 (-0.5) 0.5 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, 1], [-1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate52 : IO()
testRotate52 = 
  let q=Quat 0.0 0.0 0.7071 0.7071
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, 1], [0, 1, 0]]
  in assertClose m (quaternion2Matrix q)

testRotate53 : IO()
testRotate53 = 
  let q=Quat 0.5 (-0.5) (-0.5) (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, 1], [1, 0, 0]]
  in assertClose m (quaternion2Matrix q)

||| now test conversion between 3D rotation in opposite direction 
||| from 3x3 matrix to quaternion.
testRotateM2Q00 : IO()
testRotateM2Q00 = 
  let q=Quat 1.0 0.0 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 1, 0], [0, 0, 1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q01 : IO()
testRotateM2Q01 = 
  let q=Quat 0.7071 0.0 0.7071 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, 1, 0], [-1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q02 : IO()
testRotateM2Q02 = 
  let q=Quat 0.0 0.0 1.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 1, 0], [0, 0, -1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q03 : IO()
testRotateM2Q03 = 
  let q=Quat 0.7071 0.0 (-0.7071) 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, 1, 0], [1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q10 : IO()
testRotateM2Q10 = 
  let q=Quat 0.7071 0.0 0.0 0.7071
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [1, 0, 0], [0, 0, 1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q11 : IO()
testRotateM2Q11 = 
  let q=Quat 0.5 0.5 0.5 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [1, 0, 0], [0, 1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q12 : IO()
testRotateM2Q12 = 
  let q=Quat 0.0 0.7071 0.7071 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [1, 0, 0], [0, 0, -1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q13 : IO()
testRotateM2Q13 = 
  let q=Quat 0.5 (-0.5) (-0.5) 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [1, 0, 0], [0, -1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q20 : IO()
testRotateM2Q20 = 
  let q=Quat 0.7071 0.0 0.0 (-0.7071)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [-1, 0, 0], [0, 0, 1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q21 : IO()
testRotateM2Q21 = 
  let q=Quat 0.5 (-0.5) 0.5 (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [-1, 0, 0], [0, -1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q22 : IO()
testRotateM2Q22 = 
  let q=Quat 0.0 (-0.7071) 0.7071 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [-1, 0, 0], [0, 0,-1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q23 : IO()
testRotateM2Q23 = 
  let q=Quat 0.5 0.5 (-0.5) (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [-1, 0, 0], [0, 1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q30 : IO()
testRotateM2Q30 = 
  let q=Quat 0.7071 0.7071 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, -1], [0, 1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q31 : IO()
testRotateM2Q31 = 
  let q=Quat 0.5 0.5 0.5 (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, -1], [-1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q32 : IO()
testRotateM2Q32 = 
  let q=Quat 0.0 0.0 0.7071 (-0.7071)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, -1], [0, -1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q33 : IO()
testRotateM2Q33 = 
  let q=Quat 0.5 0.5 (-0.5) 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, -1], [1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q40 : IO()
testRotateM2Q40 = 
  let q=Quat 0.0 1.0 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, -1, 0], [0, 0, -1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q41 : IO()
testRotateM2Q41 = 
  let q=Quat 0.0 0.7071 0.0 (-0.7071)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, -1], [0, -1, 0], [-1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q42 : IO()
testRotateM2Q42 = 
  let q=Quat 0.0 0.0 0.0 1.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, -1, 0], [0, 0, 1]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q43 : IO()
testRotateM2Q43 = 
  let q=Quat 0.0 0.7071 0.0 0.7071
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 0, 1], [0, -1, 0], [1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q50 : IO()
testRotateM2Q50 = 
  let q=Quat 0.7071 (-0.7071) 0.0 0.0
      m:(Close Double => Vect 3 (Vect 3 Double))=[[1, 0, 0], [0, 0, 1], [0, -1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q51 : IO()
testRotateM2Q51 = 
  let q=Quat 0.5 (-0.5) 0.5 0.5
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, -1, 0], [0, 0, 1], [-1, 0, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q52 : IO()
testRotateM2Q52 = 
  let q=Quat 0.0 0.0 0.7071 0.7071
      m:(Close Double => Vect 3 (Vect 3 Double))=[[-1, 0, 0], [0, 0, 1], [0, 1, 0]]
  in assertClose q (matrix2Quaternion m)

testRotateM2Q53 : IO()
testRotateM2Q53 = 
  let q=Quat 0.5 (-0.5) (-0.5) (-0.5)
      m:(Close Double => Vect 3 (Vect 3 Double))=[[0, 1, 0], [0, 0, 1], [1, 0, 0]]
  in assertClose q (matrix2Quaternion m)
