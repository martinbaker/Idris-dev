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

module testAlgebra

-- Local Variables:
-- idris-load-packages: ("algebra")
-- End:
import public fieldExpression
import public finiteSet
import public perm
import public permVec
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

seperateTests0 : IO ()
seperateTests0 = putStrLn "finite set tests:"

seperateTestsCycle : IO ()
seperateTestsCycle = putStrLn "cycle tests:"

seperateTestsPerm : IO ()
seperateTestsPerm = putStrLn "permutation tests:"

seperateTestsPermVec : IO ()
seperateTestsPermVec = putStrLn "permutation vec tests:"

seperateTests1 : IO ()
seperateTests1 = putStrLn "simplify expression tests:"

seperateTests2 : IO ()
seperateTests2 = putStrLn "quaternion arithmatic tests:"

seperateTests3 : IO ()
seperateTests3 = putStrLn "rotation quaternion to matrix tests:"

seperateTests4 : IO ()
seperateTests4 = putStrLn "rotation matrix to quaternion tests:"

||| test FiniteSet
||| order is not important
testFiniteSet1 : IO()
testFiniteSet1 = 
  let fs1:(FiniteSet Integer)=fromList [1,2,3]
      fs2:(FiniteSet Integer)=fromList [3,2,1]
  in assertEq fs1 fs2

||| test FiniteSet
||| duplicates are removed
testFiniteSet2 : IO()
testFiniteSet2 = 
  let fs1:(FiniteSet Integer)=fromList [1,2,2,1,3]
      fs2:(FiniteSet Integer)=fromList [3,2,1]
  in assertEq fs1 fs2

||| test FiniteSet
||| no change union with empty set 
testFiniteSet3 : IO()
testFiniteSet3 = 
  let fs1:(FiniteSet Integer)=fromList []
      fs2:(FiniteSet Integer)=fromList [3,4,5,6,7]
      fs3:(FiniteSet Integer)=fromList [3,4,5,6,7]
      fs4:(FiniteSet Integer)=(union fs1 fs2)
  in assertEq fs3 fs4

||| test FiniteSet
||| union
testFiniteSet4 : IO()
testFiniteSet4 = 
  let fs1:(FiniteSet Integer)=fromList [1,2,3,4]
      fs2:(FiniteSet Integer)=fromList [3,4,5,6,7]
      fs3:(FiniteSet Integer)=fromList [2, 1, 3, 4, 5, 6, 7]
      fs4:(FiniteSet Integer)=(union fs1 fs2)
  in assertEq fs3 fs4

||| test FiniteSet
||| intersection with empty set is empty set 
testFiniteSet5 : IO()
testFiniteSet5 = 
  let fs1:(FiniteSet Integer)=fromList []
      fs2:(FiniteSet Integer)=fromList [3,4,5,6,7]
      fs3:(FiniteSet Integer)=fromList []
      fs4:(FiniteSet Integer)=(intersection fs1 fs2)
  in assertEq fs3 fs4

||| test FiniteSet
||| intersection
testFiniteSet6 : IO()
testFiniteSet6 =
  let fs1:(FiniteSet Integer)=fromList [1,2,3,4]
      fs2:(FiniteSet Integer)=fromList [3,4,5,6,7]
      fs3:(FiniteSet Integer)=fromList [3, 4]
      fs4:(FiniteSet Integer)=(intersection fs1 fs2)
  in assertEq fs3 fs4

||| test cycles
||| equality test - identical so equality is true
testCycle1 : IO()
testCycle1 =
  let cy1 : Cycle Nat = fromList [1,2,3,4]
      cy2 : Cycle Nat = fromList [1,2,3,4]
  in assertEq (cy1 ==cy2) True

||| test cycles
||| equality test - rotate 1 right so equality is true
testCycle2 : IO()
testCycle2 =
  let cy1 : Cycle Nat = fromList [1,2,3,4]
      cy2 : Cycle Nat = fromList [4,1,2,3]
  in assertEq (cy1==cy2) True

||| test cycles
||| equality test - rotate 2 right so equality is true
testCycle3 : IO()
testCycle3 =
  let cy1 : Cycle Nat = fromList [1,2,3,4]
      cy2 : Cycle Nat = fromList [3,4,1,2]
  in assertEq (cy1==cy2) True

||| test cycles
||| equality test - rotate 3 right so equality is true
testCycle4 : IO()
testCycle4 =
  let cy1 : Cycle Nat = fromList [1,2,3,4]
      cy2 : Cycle Nat = fromList [2,3,4,1]
  in assertEq (cy1==cy2) True

||| test cycles
||| equality test - this equality fails because we can't get
||| from one to the other by rotating
testCycle5 : IO()
testCycle5 =
  let cy1 : Cycle Nat = fromList [1,2,3,4]
      cy2 : Cycle Nat = fromList [1,3,2,4]
  in assertEq (cy1==cy2) False

||| test cycles
||| cycle -> permutation -> cycle
||| We should get back to same place when we convert cycle to
||| permutation and back.
testCycle6 : IO()
testCycle6 =
  let cyl : List (Cycle Nat) = [fromList [1,2],fromList [3,4,5]]
      prm : Permutation Nat = cyclesToPermutation cyl
      cy2 : List (Cycle Nat) = cyclesFromPermutation prm
  in assertEq cyl cy2

||| test cycles
||| cycle -> permutation -> cycle
||| A fixpoint should be removed.
testCycle7 : IO()
testCycle7 =
  let cyl : List (Cycle Nat) = [fromList [1]]
      prm : Permutation Nat = cyclesToPermutation cyl
      cy2 : List (Cycle Nat) = cyclesFromPermutation prm
  in assertEq cy2 Nil

||| test cycles
||| cycle -> permutation -> cycle
||| Error condition - in a permutation an element should not
||| occur more than once, if it does dont include cycle with
||| duplicate element
testCycle8 : IO()
testCycle8 =
  let cyl : List (Cycle Nat) = [fromList [1,2],fromList [2,3,4]]
      prm : Permutation Nat = cyclesToPermutation cyl
      cy2 : List (Cycle Nat) = cyclesFromPermutation prm
      cy3 : List (Cycle Nat) = [fromList [1,2]]
  in assertEq cy2 cy3

||| test Permutations
||| remove fixpoints
testPermutation1 : IO()
testPermutation1 = 
  let p=permSetFromList [1,2,3,4] [3,2,1,4]
      p2=permSetFromList [1,3] [3,1]
  in assertEq p p2

||| test Permutations
||| multiply (compose)
testPermutation2 : IO()
testPermutation2 = 
  let p=permSetFromList [1,3] [3,1]
      p2=permSetFromList [1,2] [2,1]
      p3=permSetFromList [1, 2, 3] [3, 1,2]
  in assertEq p3 (p*p2)

||| permVec - test invert
testPermVec1 : IO()
testPermVec1 = 
  let
    mp:(FiniteSet String) = fromList ["a","b","c"]
    perms:(List (List Nat)) = [[1,2,3],[2,3,1]]
    perms2:(List (List Nat)) = [[3,2,1],[1,3,2]]
    p:PermutationVec String = PermVec mp perms
    pi:PermutationVec String = permVec.invert p
    p2:PermutationVec String = PermVec mp perms2
  in assertEq pi p2

||| permVec - test invert is an involution.
testPermVec2 : IO()
testPermVec2 = 
  let
    mp:(FiniteSet String) = fromList ["a","b","c"]
    perms:(List (List Nat)) = [[1,2,3],[2,3,1]]
    p:PermutationVec String = PermVec mp perms
    p2:PermutationVec String = permVec.invert (permVec.invert p)
  in assertEq p p2


||| test simplify expression
||| 1+2=3
testExpressionSimplify1 : IO()
testExpressionSimplify1 = 
  let e1 = LitFloat 1.0
      e2 = LitFloat 2.0
      e3 = LitFloat 3.0   
  in assertEq e3 (simplify (fieldexp.(+) e1 e2))

||| test simplify expression
||| 1-2=-1
testExpressionSimplify2 : IO()
testExpressionSimplify2 = 
  let e1 = LitFloat 1.0
      e2 = LitFloat 2.0
      e3 = LitFloat (-1.0)
  in assertEq e3 (simplify (fieldexp.(-) e1 e2))

||| test simplify expression
||| 2*3=6
testExpressionSimplify3 : IO()
testExpressionSimplify3 = 
  let e1 = LitFloat 2.0
      e2 = LitFloat 3.0
      e3 = LitFloat 6.0   
  in assertEq e3 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| 6/3=2
testExpressionSimplify4 : IO()
testExpressionSimplify4 = 
  let e1 = LitFloat 6.0
      e2 = LitFloat 3.0
      e3 = LitFloat 2.0   
  in assertEq e3 (simplify (fieldexp.(/) e1 e2))

||| test simplify expression
||| 0+x=x
testExpressionSimplify5 : IO()
testExpressionSimplify5 = 
  let e1 = LitFloat 0.0
      e2 = VarFloat "x"   
  in assertEq e2 (simplify (fieldexp.(+) e1 e2))

||| test simplify expression
||| x+0=x
testExpressionSimplify6 : IO()
testExpressionSimplify6 = 
  let e1 = VarFloat "x"
      e2 = LitFloat 0.0  
  in assertEq e1 (simplify (fieldexp.(+) e1 e2))

||| test simplify expression
||| x-0=x
testExpressionSimplify7 : IO()
testExpressionSimplify7 = 
  let e1 = VarFloat "x"
      e2 = LitFloat 0.0  
  in assertEq e1 (simplify (fieldexp.(-) e1 e2))

||| test simplify expression
||| 0-x=-x
testExpressionSimplify8 : IO()
testExpressionSimplify8 = 
  let e1 = LitFloat 0.0
      e2 = VarFloat "x"
      e3 = Function "negate" [e2]  
  in assertEq e3 (simplify (fieldexp.(-) e1 e2))

||| test simplify expression
||| x*1=x
testExpressionSimplify9 : IO()
testExpressionSimplify9 = 
  let e1 = VarFloat "x"
      e2 = LitFloat 1.0  
  in assertEq e1 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| 1*x=x
testExpressionSimplify10 : IO()
testExpressionSimplify10 = 
  let e1 = LitFloat 1.0
      e2 = VarFloat "x"   
  in assertEq e2 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| x/1=x
testExpressionSimplify11 : IO()
testExpressionSimplify11 = 
  let e1 = VarFloat "x"
      e2 = LitFloat 1.0  
  in assertEq e1 (simplify (fieldexp.(/) e1 e2))

||| test simplify expression
||| 1/x=inv x
testExpressionSimplify12 : IO()
testExpressionSimplify12 = 
  let e1 = LitFloat 1.0
      e2 = VarFloat "x"
      e3 = Function "inv" [e2] 
  in assertEq e3 (simplify (fieldexp.(/) e1 e2))

||| test simplify expression
||| x*0=0
testExpressionSimplify13 : IO()
testExpressionSimplify13 = 
  let e1 = VarFloat "x"
      e2 = LitFloat 0.0  
  in assertEq e2 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression
||| 0*x=0
testExpressionSimplify14 : IO()
testExpressionSimplify14 = 
  let e1 = LitFloat 0.0
      e2 = VarFloat "x"   
  in assertEq e1 (simplify (fieldexp.(*) e1 e2))

||| test simplify expression - compound
||| x*(x-x) = 0
testExpressionSimplify15 : IO()
testExpressionSimplify15 = 
  let e1 = VarFloat "x"
      e2 = LitFloat 0.0  
  in assertEq e2 (simplify (fieldexp.(*) e1 (fieldexp.(-) e1 e1)))

||| test simplify expression
||| x + Undefined = Undefined
testExpressionSimplify16 : IO()
testExpressionSimplify16 = 
  let e1 = Undefined
      e2 = VarFloat "x" 
  --in assertEq e1 (simplify (fieldexp.(+) e1 e1))
  in assertEq e1 (simplify (fieldexp.(+) e1 e2))

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
