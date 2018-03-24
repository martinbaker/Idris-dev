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

||| Implements multiple permutations (subgroups of bijections of a set).
||| Represents the permutation as a set together with a map defined
||| by a list of indexes into the set.
record PermutationVec set where
   constructor PermVec
   mp:(FiniteSet set)
   perms:(List (List Nat))

||| auxilary constructor - unit
||| This constructs the special permutation that does nothing.
unitv : Eq s => PermutationVec s
unitv = PermVec empty empty

||| eval returns the image of element (el) under the
||| permutation p.
||| @p single permutation as a list of indexes
||| @el element index to be evaluated
evalv : (p : (List Nat)) -> (el : Nat) -> Nat
evalv p el =
  case List.index' el p of
    Nothing => el
    Just x => x

||| Multiplcation of permutations represents composition.
||| That is the result is the same a taking the first permutation
||| and applying the second permutation to the result of the first.
||| This is made more complicated because the code needs to insert
||| any points which are fixpoints in one operand but not the other.
(*) : (List Nat) -> (List Nat) -> (List Nat)
(*) q p =
  compose q p
    where
      compose : (List Nat) -> (List Nat) -> (List Nat)
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

||| Attempt to find the nth element of a set.
||| If the provided index is out of bounds, return Nothing.
||| Only valid for cases of set where order is significant
elementAt : (n : Nat) -> (l : List Nat) -> Nat
elementAt Z     (x::xs) = x --Just x
elementAt (S n) (x::xs) = elementAt n xs
elementAt _ [] = 0 --Nothing

||| local function for invert
invertInd : Nat ->  (List Nat) -> (List Nat) -> (List Nat)
invertInd i v soFar =
  if (length soFar) == (length v)
  then soFar
  else invertInd (S i) v ((elementAt i v)::soFar)

||| local function for invert
inv : List (List Nat) -> List (List Nat)
inv [] = []
inv (v::vs) = (invertInd Z v Nil)::(inv vs)

||| invert permutation, that is, reverse all generators.
||| @p permutation to be inverted
invert : Eq s => (p : (PermutationVec s)) -> (PermutationVec s)
invert p =
  let
   points : FiniteSet s = mp p
   indexes : List (List Nat) = perms p
   invIndexes : List (List Nat) = inv indexes
  in PermVec points invIndexes

||| covert a preimage-image instance of permutation to a vector type
||| @p preimage-image instance of permutation to be converted.
||| @allMoved FiniteSet containing all points that are moved by permutations.
|||           result will index into this list.
permToVectSingle : Eq s => (p : (Permutation s)) ->
                           (allMoved : (FiniteSet s)) ->
                           (List Nat)
permToVectSingle p allMoved =
  let
    preIm :(FiniteSet s) = preimage p
    preImIndex : List Nat = finiteSetToIndex allMoved preIm
    im:(FiniteSet s) = image p
    imIndex : List Nat = finiteSetToIndex allMoved im
  in mapIndex Z preImIndex imIndex (order allMoved)
    where
      mapIndex : (n:Nat) ->
                 (preImIndex : List Nat) ->
                 (imIndex : List Nat) ->
                 (siz : Nat) ->
                 (List Nat)
      mapIndex n preImIndex imIndex siz =
        let
          a : Nat = case (elemIndex n preImIndex) of
            Nothing => n
            Just b => elementAt b imIndex
        in 
          if
            (S n) >= siz
          then
            [a]
          else
            a::(mapIndex (S n) preImIndex imIndex siz)

||| covert a list of preimage-image permutations to a vector type
||| @p1 preimage-image instance of permutation to be converted
||| @allMoved union of all points that move.
permToVect1 : Eq s => (p1 : List (Permutation s)) -> (allMoved : (FiniteSet s)) -> (List (List Nat))
permToVect1 Nil allMoved = Nil
permToVect1 (p::ps) allMoved = (permToVectSingle p allMoved)::(permToVect1 ps  allMoved)

||| A union of all the points moved in a set of permutations
||| @p2 preimage-image instance of permutation to be converted
movedPointsInPerms : Eq s => (p2 : List (Permutation s)) -> (FiniteSet s)
movedPointsInPerms Nil = empty
movedPointsInPerms (p::ps) = union (preimage p) (movedPointsInPerms ps)

||| covert a list of preimage-image permutations to a vector type
||| @p preimage-image instance of permutation to be converted
permToVect : Eq s => (p : List (Permutation s)) -> (PermutationVec s)
permToVect p = 
  let
    pPreIm :(FiniteSet s) = movedPointsInPerms p
    mapping : List (List Nat) = permToVect1 p pPreIm
  in PermVec pPreIm mapping

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
    ((mp a) == (mp b)) && ((perms a) == (perms b))

implementation Show s => Show (PermutationVec s) where
    show a = "permVec " ++(show (mp a)) ++ (show (perms a))
