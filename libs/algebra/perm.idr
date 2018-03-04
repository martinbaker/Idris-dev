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
-- to use Idris type system to make them impossible.
--import Effects
import public finiteSet
import public cycle
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

||| An auxilary constructor where the preImage and Image are
||| provided in the form of lists.
permSetFromList : Eq set => (preim:List set) ->
                  (im:List set) ->
                  Permutation set
permSetFromList preim im =
  permSet (fromList preim) (fromList im)

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
    image2Set:(FiniteSet s) = multiLookup image1Set pSet pSet2
  in permSet fullSet image2Set

||| movedPoints(p) returns the set of points moved by the permutation p.
||| @p permutation
movedPoints : Eq s => (p : (Permutation s)) -> (FiniteSet s)
movedPoints p =
  FiniteSet.mPoints (preimage p) (image p) FiniteSet.empty

||| degree(p) retuns the number of points moved by the
||| permutation p.
||| @p permutation
degree : Eq s => (p : (Permutation s)) ->  Nat
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

{-
||| A list of cycles can represent a permutation.
||| In fact a list of cycles is a very compact notation.
cyclesToPermutation : List (Cycle elem) -> (Permutation s)
cyclesToPermutation l =
-}

||| Return True if both the preimage and image are the same (but they can
||| be reordered and still be True provided preimage and image are
||| reordered in the same way).
implementation (Eq s) => Eq (Permutation s) where
  (==) a b = 
    if (preimage a) == (preimage b)
    then
      let
        m:(FiniteSet s) = multiLookup (preimage a) (preimage b) (image b)
      in
        identical m (image a)
    else False

implementation Show s => Show (Permutation s) where
    show a = "permutation" ++(show (preimage a)) ++ (show (image a))
