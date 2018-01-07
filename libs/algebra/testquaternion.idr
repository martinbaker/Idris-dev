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

||| test multipication - first axioms
||| i*i = j*j = k*k = i*j*k = -1
test1 : IO()
test1 = 
  let qi=Quat 0.0 1.0 0.0 0.0
  in putStrLn ("i*i="++ show(qi*qi))
 
test2 : IO()
test2 = 
  let qj=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("j*j="++ show(qj*qj))

test3 : IO()
test3 = 
  let qk=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("k*k="++ show(qk*qk))
 
test4 : IO()
test4 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("i*j*k="++ show(qi*(qj*qk)))

||| test multipication - multiplcation by reals
test5 : IO()
test5 = 
  let qr=Quat 1.0 0.0 0.0 0.0
  in putStrLn ("r*r="++ show(qr*qr))
 
test6 : IO()
test6 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qi=Quat 0.0 1.0 0.0 0.0
  in putStrLn ("r*i=:"++ show(qr*qi))
 
test7 : IO()
test7 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("r*j="++ show(qr*qj))
 
test8 : IO()
test8 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("r*k="++ show(qr*qk))
 
test9 : IO()
test9 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qi=Quat 0.0 1.0 0.0 0.0
  in putStrLn ("i*r=:"++ show(qi*qr))
 
test10 : IO()
test10 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("j*r="++ show(qj*qr))
 
test11 : IO()
test11 = 
  let qr=Quat 1.0 0.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("k*r="++ show(qk*qr))

||| test multipication - multiplcation of different
||| imaginary axes anticommute
test12 : IO()
test12 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("i*j="++ show(qi*qj))
 
test13 : IO()
test13 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qj=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("j*i="++ show(qj*qi))
 
test14 : IO()
test14 = 
  let qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("j*k="++ show(qj*qk))
 
test15 : IO()
test15 = 
  let qj=Quat 0.0 0.0 1.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("k*j="++ show(qk*qj))
 
test16 : IO()
test16 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("i*k="++ show(qi*qk))
 
test17 : IO()
test17 = 
  let qi=Quat 0.0 1.0 0.0 0.0
      qk=Quat 0.0 0.0 0.0 1.0
  in putStrLn ("k*i="++ show(qk*qi))

||| test addition
test18 : IO()
test18 = 
  let qa=Quat 1.0 2.0 3.0 4.0
      qb=Quat 1.0 1.0 1.0 1.0
  in putStrLn ("(1+i2+j3+k4)+(1+i+j+k)="++ show(qa+qb))

||| test subtract
test19 : IO()
test19 = 
  let qa=Quat 1.0 2.0 3.0 4.0
      qb=Quat 1.0 1.0 1.0 1.0
  in putStrLn ("(1+i2+j3+k4)-(1+i+j+k)="++ show(qa-qb))

||| test conversion between 3D rotation representations
||| using quaternions or 3x3 matrix.
test20 : IO()
test20 = 
  let qIden=Quat 1.0 0.0 0.0 0.0
  in putStrLn ("no rotation =1 ="++ show(quaternion2Matrix qIden))

test21 : IO()
test21 = 
  let qy90=Quat 0.7071 0.0 0.7071 0.0
  in putStrLn ("y90 = 0.7071 + j 0.7071 ="++ show(quaternion2Matrix qy90))

test22 : IO()
test22 = 
  let qy180=Quat 0.0 0.0 1.0 0.0
  in putStrLn ("y180 = j ="++ show(quaternion2Matrix qy180))

test23 : IO()
test23 = 
  let qy270=Quat 0.7071 0.0 (-0.7071) 0.0
  in putStrLn ("y270 = 0.7071 - 0.7071 ="++ show(quaternion2Matrix qy270))
