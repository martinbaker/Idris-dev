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
--import Effect.Exception
import public finiteSet
import public cycle

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
||| @p permutation under consideration
||| @el element to start orbit
orbit : Eq s => (p : (Permutation s)) -> (el : s) -> (FiniteSet s)
orbit p el = reverse (buildOrbit p el el (fromList [el]) Z)
  where
    ||| build an orbit recursivly
    ||| @p permutation under consideration
    ||| @el current element in orbit
    ||| @fstEl first element in orbit
    ||| @orbBuild orbit under construction
    ||| @loopBreaker counter to prevent infinite loops
    buildOrbit : Eq s => (p : (Permutation s)) ->
                         (el : s) ->
                         (fstEl : s) ->
                         (orbBuild : (FiniteSet s)) ->
                         (loopBreaker : Nat) ->
                         (FiniteSet s)
    buildOrbit p el fstEl orbBuild loopBreaker = 
      let el2:s = eval p el
      in if fstEl==el2 || loopBreaker>100
         then orbBuild
         else buildOrbit p el2 fstEl (insert el2 orbBuild) (S loopBreaker)


||| A list of cycles can represent a permutation.
||| In fact a list of cycles is a very compact notation.
cyclesToPermutation : (Eq s) => List (Cycle s) -> (Permutation s)
cyclesToPermutation l =
  let
    (preim,im) : ((List s),(List s)) = cyclesToPreImImage l
  in
    permSetFromList preim im

{-
||| This is a local function which is used by cyclesFromPermutation
||| to find an element that is not yet in a cycle.
unusedElement : (Eq s) => (Permutation s) ->
                          (List (Cycle s)) ->
                          Maybe s
unusedElement p lc =
  let
    preSet: FiniteSet s = preimage p
    usedSoFar : FiniteSet s = fromList (cyclesAllElements lc)
    diff: FiniteSet s = difference preSet usedSoFar
  in first diff
-}

||| generate remaining cycles from permutation
||| @p permutation to be converted to cycles.
||| @notYetConv set of elements not yet included in cycles
||| @f1 first element of notYetConv
||| @cyclesSoFar add additional cycles to this
||| @loopBreaker just used to prevent infinite loops
generateCycles : (Eq s) => (p : (Permutation s)) ->
                           (notYetConv : (FiniteSet s)) ->
                           (f1 : s) ->
                           (cyclesSoFar : List (Cycle s)) ->
                           (loopBreaker : Nat) ->
                           List (Cycle s)
generateCycles p notYetConv f1 cyclesSoFar loopBreaker =
  let
    orb : FiniteSet s = orbit p f1 -- orbit gives new cycle
    orbList : List s = toList orb
    cy : Cycle s = fromList orbList -- convert orbit to cycle
    c : List (Cycle s) = cy::cyclesSoFar
    usedSoFar : FiniteSet s = fromList (cyclesAllElements c)
    diff: FiniteSet s = difference notYetConv usedSoFar
    -- diff contains elements not yet in cycles
    f:Maybe s = first diff
  in
    if loopBreaker>1000
    then c
    else case f of
      Nothing => c
      Just a => generateCycles p diff a c (S loopBreaker)

||| Convert a list of cycles to a permutation.
cyclesFromPermutation : (Eq s) => (Permutation s) ->
                                   List (Cycle s)
cyclesFromPermutation p =
  let
    preSet:(FiniteSet s) = preimage p
    firstEle : Maybe s = first preSet
  in case firstEle of
    Nothing => Nil
    Just a => reverse (generateCycles p preSet a Nil Z)

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
