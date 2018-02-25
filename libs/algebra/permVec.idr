{-
 - (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 licence but if there were any interest in including
 - this with Idris library then a compatible licence would be acceptable.
 - 
 - This code implements Permutations (subgroups of bijections
 - of a set) using Idris.
 -
 - A given permutation can represent an element of a group.
 - Composition of permutations will then represent the groups
 - multiplication operetion. Which is why concatination is
 - implemented here as (*) operator.
 -
 - Here we consider alternative ways to represent a permutation type such as:
 - * 'preimage-image' coding.
 - * 'vector' coding.
 - * 'cycle' notation.
 - Since they all have pros and cons we need to consider the
 - coding for both and how to convert between them.
 -
 - For an explanation with example session see this page:
 - http://www.euclideanspace.com/prog/scratchpad/mycode/discrete/finiteGroup/perm/
 - for more general information about objectives see this page:
 - http://www.euclideanspace.com/prog/idris/
 -}

module permVec

-- For now we need to have some runtime errors. I cant work out how
-- to use Idris type system to make then impossible.
--import Effects
import public finiteSet
import public perm
--import Effect.Exception

%access public export

||| Implements permutations (subgroups of bijections of a set).
||| Represents the permutation as a set together with a map defined
||| by a list of indexes into the set.
record PermutationVec set where
   constructor PermVec
   mp:(FiniteSet set)
   map:(List Nat)

||| auxilary constructor - unit
||| This constructs the special permutation that does nothing.
unitv : Eq s => PermutationVec s
unitv = PermVec empty empty

||| eval returns the image of element (el) under the
||| permutation p.
||| @p permutation
||| @el element index
evalv : Eq s => (p : (PermutationVec s)) -> (el : Nat) -> Nat
evalv p el =
  case List.index' el (map p) of
    Nothing => el
    Just x => x

||| Multiplcation of permutations represents composition.
||| That is the result is the same a taking the first permutation
||| and applying the second permutation to the result of the first.
||| This is made more complicated because the code needs to insert
||| any points which are fixpoints in one operand but not the other.
(*) : Eq s => (PermutationVec s) -> (PermutationVec s) -> (PermutationVec s)
(*) q p =
  let
    qMp :(FiniteSet s) = mp q
    qMap:(List Nat) = map q
  in PermVec qMp (compose qMap p)
    where
      compose : (List Nat) -> (PermutationVec s) -> (List Nat)
      compose Nil _ = Nil
      compose (q::qs) p = (evalv p q)::(compose qs p)

||| movedPoints(p) returns the set of points moved by the permutation p.
||| @p permutation
movedPoints : Eq s => (p : (PermutationVec s)) -> (FiniteSet s)
movedPoints p = mp p

||| degree(p) retuns the number of points moved by the
||| permutation p.
||| @p permutation
degree : Eq s => (p : (PermutationVec s)) ->  Nat
degree p = order (movedPoints p)

||| covert a preimage-image instance of permutation to a vector type
||| @p preimage-image instance of permutation to be converted
permToVect : Eq s => (p : (Permutation s)) -> (PermutationVec s)
permToVect p =
  let
    pPreIm :(FiniteSet s) = preimage p
    pPreImList :(List s) = toList pPreIm
    pIm:(FiniteSet s) = image p
  in PermVec pPreIm (mapIndex Z pPreImList p)  
    where
      mapIndex : Nat -> (List s) -> (Permutation s) -> (List Nat)
      mapIndex _ Nil _ = Nil
      mapIndex n (q::qs) p =
        let
          pPreIm :(FiniteSet s) = preimage p
          pIm:(FiniteSet s) = image p
        in (lookupIndexed n pPreIm pIm)::(mapIndex (S n) qs p)

{-||| orbit returns the orbit of element (el) under the
||| permutation p, i.e. the set which is given by applications of
||| the powers of p to el.
||| @p permutation
||| @el element
orbit : Eq s => (p : (PermutationVec s)) -> (el : s) -> (FiniteSet s)
orbit p el = buildOrbit p el empty
  where
    buildOrbit : Eq s => (p : (PermutationVec s)) -> (el : s) -> (FiniteSet s) -> (FiniteSet s)
    buildOrbit p el orbBuild = 
      let el2:s = eval p el
      in if el==el2
         then orbBuild
         else buildOrbit p el2 (insert el2 orbBuild)
-}

||| Return True if both the mp and map are the same but they can
||| be reordered and still be True provided mp and map are
||| reordered in the same way.
implementation (Eq s) => Eq (PermutationVec s) where
  (==) a b = 
    ((mp a) == (mp b)) && ((map a) == (map b))

implementation Show s => Show (PermutationVec s) where
    show a = "permVec " ++(show (mp a)) ++ (show (map a))
