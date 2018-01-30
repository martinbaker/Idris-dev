{-
 - (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 licence but if there were any interest in including
 - this with Idris library then a compatible licence would be acceptable.
 - 
 - This code implements Permutations (subgroups of bijections
 - of a set) using Idris.
 - For an explanation with example session see this page:
 - http://www.euclideanspace.com/prog/idris/quaternion/
 - for more general information about objectives see this page:
 - http://www.euclideanspace.com/prog/idris/
 - 
 - Some of the ideas for this come from a program called 'Axiom'
 - which contains a permutation implementation authored by
 - Holger Gollan, Johannes Grabmeier, Gerhard Schneider
 - and first created: 27 July 1989. A fork of this program is
 - here:
 - https://github.com/fricas/fricas/blob/master/src/algebra/perm.spad
 - I have not used this code directly, just some of the concepts.
 -}

module perm

%access public export

||| Implements permutations (subgroups of bijections of a set).
||| Represents the permutation p as a list of preimages and images, i.e
||| p maps preimage to image for all indices k. Elements of set not
||| in preimage are fixed points, and these are the only fixed points
||| of the permutation.
record Permutation set where
   constructor Perm
   preimage:(List set)
   image:(List set)

--smallerElement : Ord S => S -> S -> Bool
--smallerElement a b = a<b

{-rotate : Nat -> (List a) -> (List a)
rotate _ [] = []
rotate n xs = zipWith 2 (List.drop n (cycle xs)) xs
Idris> :let l=[1,2,3,4]
Idris> l
[1, 2, 3, 4] : List Integer
Idris> :let l2=drop 2 l
Idris> l2
[3, 4] : List Integer
Idris> :let l3=take 2 l
Idris> l3
[1, 2] : List Integer
Idris> l2++l3
[3, 4, 1, 2] : List Integer
Idris> -}



--||| index of minimum value
--elemIndex  (minimum a) a

||| smallest element is put in first place
||| doesn't change cycle if underlying set
||| is not ordered or not finite.
rotateCycle : (List s) -> (List s)
rotateCycle [] = []
rotateCycle cyc =
  cyc
--  let minIndex:Int = elemIndex  (minimum cyc) cyc
--  in zipWith const (drop minIndex (cycle cyc)) cyc
  
{-      min : S := first cyc
      minpos : I := 1           -- 1 = minIndex cyc
      for i in 2..maxIndex cyc repeat
        if smallerElement?(cyc.i, min) then
          min  := cyc.i
          minpos := i
      (minpos = 1) => cyc
      concat(last(cyc, ((#cyc-minpos+1)::NNI)), first(cyc, (minpos-1)::NNI))-}

