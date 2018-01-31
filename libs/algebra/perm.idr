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

||| find index of the smallest element of a list
lowerBoundIndex : Ord s => List s -> Maybe Nat
lowerBoundIndex [] = Nothing
lowerBoundIndex lst =
  let y:(Maybe s) = lowerBound lst Nothing
  in case y of
    Nothing => Nothing
    Just z1 => elemIndex z1 lst
  where
      -- find the smallest element of a list
      lowerBound : Ord s => List s -> Maybe s -> Maybe s
      lowerBound [] w = w
      lowerBound (x::xs) Nothing =
        lowerBound xs (Just x)
      lowerBound (x::xs) (Just n) =
        let y:(Maybe s) = lowerBound xs (Just x)
            z:s = case y of
              Nothing => n
              Just z1 => z1
        in if n < z  then (Just n) else (Just z)

||| smallest element is put in first place
||| doesn't change cycle if underlying set
||| is not ordered or not finite.
rotateCycle : Ord s => (List s) -> (List s)
rotateCycle [] = []
rotateCycle cyc =
  let lbi:(Maybe Nat) = lowerBoundIndex cyc
  in case lbi of
    Nothing => cyc
    Just z1 =>
      let f=List.drop z1 cyc
          l=take z1 cyc
      in f++l

||| eval returns the image of element (el) under the
||| permutation p.
||| @p permutation
||| @el element
eval  : Ord s => (p : (Permutation s)) -> (el : s) -> (Maybe s)
eval p el =
  let i:(Maybe Nat) = elemIndex el (preimage p)
  in case i of
    Nothing => Nothing
    Just z1 => index' z1 (preimage p)

||| movedPoints(p) returns the set of points moved by the permutation p.
||| @p permutation
movedPoints : (p : (Permutation s)) -> (List s)
movedPoints p = preimage p

||| degree(p) retuns the number of points moved by the
||| permutation p.
||| @p permutation
degree : (p : (Permutation s)) ->  Nat
degree p =  length (movedPoints p)

||| orbit returns the orbit of element (el) under the
||| permutation p, i.e. the set which is given by applications of
||| the powers of p to el.
||| @p permutation
||| @el element
orbit : Ord s => (p : (Permutation s)) -> (el : s) -> (List s)
orbit p el = buildOrbit p el [el]
  where
    buildOrbit : Ord s => (p : (Permutation s)) -> (el : s) -> (List s) -> (List s)
    buildOrbit p el orbBuild = 
      let el2:(Maybe s) = eval p el
      in case el2 of
        Nothing => orbBuild
        Just el2j => if el==el2j
                     then orbBuild
                     else buildOrbit p el2j orbBuild++[el2j]



