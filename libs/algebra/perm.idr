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

-- For now we need to have some runtime errors. I cant work out how
-- to use Idris type system to make then impossible.
--import Effects
import public finiteSet
--import Effect.Exception

%access public export

||| Implements permutations (subgroups of bijections of a set).
||| Represents the permutation p as a list of preimages and images, i.e
||| p maps preimage to image for all indices k. Elements of set not
||| in preimage are fixed points, and these are the only fixed points
||| of the permutation.
record Permutation set where
   constructor Perm
   preimage:(FiniteSet set)
   image:(FiniteSet set)

||| auxilary constructor - unit
||| This constructs the special permutation that does nothing.
unit : Eq s => Permutation s
unit = Perm empty empty

||| An auxilary constructor that ensures fixpoints are not included.
||| It is therefore safer to use this constructor than the default.
permSet : Eq set => (preim:(FiniteSet set)) ->
                  (im:(FiniteSet set)) ->
                  Permutation set
permSet preim im =
  let m = dropFixpoint preim im
  in Perm (fst m) (snd m)

||| eval returns the image of element (el) under the
||| permutation p.
||| @p permutation
||| @el element
eval : Eq s => (p : (Permutation s)) -> (el : s) -> s
eval p el = lookup el (preimage p) (image p)

||| Multiplcation of permutations represents composition.
||| That is the result is the same a taking the first permutation
||| and applying the second permutation to the result of the first.
||| This is made more complicated because the code needs to insert
||| any points which are fixpoints in one operand but not the other.
(*) : Eq s => (Permutation s) -> (Permutation s) -> (Permutation s)
(*) q p =
  let
    qSet:(FiniteSet s) = preimage q
    qSet2:(FiniteSet s) = image q
    pSet:(FiniteSet s) = preimage p
    pSet2:(FiniteSet s) = image p
    fullSet:(FiniteSet s) = union qSet pSet
    image1Set:(FiniteSet s) = multiLookup fullSet qSet qSet2
    image2Set:(FiniteSet s) = multiLookup image1Set qSet qSet2
  in permSet fullSet image2Set

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

{-
||| runtime error for the EXCEPTION effect declared in module Effect.Exception.
data Error = CycleContainsDuplicates
-}

||| cycle coerces a cycle {\em ls}, i.e. a list without
||| repetitions to a permutation, which maps {\em ls.i} to
||| {\em ls.i+1}, indices modulo the length of the list.
||| Error: if repetitions occur.
cycle : Ord s => List s -> Permutation s
cycle [] = unit -- zero elements cant contain a cycle
cycle (x::[]) = unit -- one element cant contain a cycle
cycle (x::xs) =
  --duplicates? ls => raise CycleContainsDuplicates
  Perm (fromList (x::xs)) (fromList (xs++[x]))

||| cycles coerces a list list of cycles lls
||| to a permutation, each cycle being a list with not
||| repetitions, is coerced to the permutation, which maps
||| ls.i to ls.i+1, indices modulo the length of the list,
||| then these permutations are mutiplied.
||| Error: if repetitions occur in one cycle.
cycles : Ord s => List(List s)  -> Permutation s
cycles lls =
  unit

{-  perm : % := 1
  for lists in reverse lls repeat
    perm := cycle lists * perm
  perm-}

||| movedPoints(p) returns the set of points moved by the permutation p.
||| @p permutation
movedPoints : (p : (Permutation s)) -> (FiniteSet s)
movedPoints p = preimage p

||| degree(p) retuns the number of points moved by the
||| permutation p.
||| @p permutation
degree : (p : (Permutation s)) ->  Nat
degree p = order (movedPoints p)

||| orbit returns the orbit of element (el) under the
||| permutation p, i.e. the set which is given by applications of
||| the powers of p to el.
||| @p permutation
||| @el element
orbit : Eq s => (p : (Permutation s)) -> (el : s) -> (FiniteSet s)
orbit p el = buildOrbit p el empty
  where
    buildOrbit : Eq s => (p : (Permutation s)) -> (el : s) -> (FiniteSet s) -> (FiniteSet s)
    buildOrbit p el orbBuild = 
      let el2:s = eval p el
      in if el==el2
         then orbBuild
         else buildOrbit p el2 (insert el2 orbBuild)

