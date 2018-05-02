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

||| This code implements Permutations (subgroups of bijections
||| of a set) in an indexed form which is easier to work with
||| than the preimage-image form.
module permsIndexed

-- For now we need to have some runtime errors. I cant work out how
-- to use Idris type system to make then impossible.
--import Effects
import public finiteSet
import public perm
import public permIndexedElement
--import Effect.Exception

%access public export

||| Implements multiple permutations (subgroups of bijections of a set).
||| Represents the permutation as a set together with a map defined
||| by a list of indexes into the set.
record PermsIndexed set (x:(FiniteSet set)) where
   constructor MkPermsIndex
   --perms:(List (List Nat))
   gensIndexed : List PermIndexedElement

||| zip up permutations only
MkPermsIndexed : (List (List Nat)) -> (PermsIndexed set fs)
MkPermsIndexed Nil = MkPermsIndex []
MkPermsIndexed m = MkPermsIndex (mpi m) where
  mpi : (List (List Nat)) -> List PermIndexedElement
  mpi Nil = Nil
  mpi (x::xs) = (PIE x [] 0)::(mpi xs)


||| unzip to permutations only
||| used in show and == (should really find a beeter way)
perms : (PermsIndexed set fs) -> (List (List Nat))
perms p = perms' (gensIndexed p) where
  perms' : (List PermIndexedElement) -> (List (List Nat))
  perms' Nil = Nil
  perms' (x::xs) =
    (elt x)::(perms' xs)

||| auxilary constructor - unit
||| This constructs the special permutation that does nothing.
unitv : Eq s => PermsIndexed s empty
unitv = MkPermsIndexed Nil

{-
||| eval returns the image of element (el) under the
||| permutation p.
||| @p single permutation as a list of indexes
||| @el element index to be evaluated
evalv : (p : (List Nat)) -> (el : Nat) -> Nat
evalv p el =
  case List.index' el p of
    Nothing => el
    Just x => x
-}

getPoints : {fs:(FiniteSet set)} -> (PermsIndexed set fs) -> (FiniteSet set)
getPoints y = fs

{-
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
-}

||| movedPoints(p) returns the set of points moved by the permutation p.
||| @p permutation
movedPoints : Eq s => {fs:(FiniteSet s)} -> (p : (PermsIndexed s fs)) -> (FiniteSet s)
movedPoints p = fs -- was mp p

||| degree(p) retuns the number of points moved by the
||| permutation p.
||| @p permutation
degree : Eq s => {fs:(FiniteSet s)} -> (p : (PermsIndexed s fs)) ->  Nat
degree p = order (movedPoints p)

||| invert permutation, that is, reverse all generators.
||| @p permutation to be inverted
invert : Eq s => {fs:(FiniteSet s)} -> (p : (PermsIndexed s fs)) -> (PermsIndexed s fs)
invert p =
  let
   --points : FiniteSet s = fs -- was mp p
   indexes : List PermIndexedElement = gensIndexed p
  in MkPermsIndex (inv indexes) where
    ||| local function for invert
    inv : List PermIndexedElement -> List PermIndexedElement
    inv [] = []
    inv (v::vs) = (invertEle v)::(inv vs)

elemAt : (n : Nat) -> (l : List Nat) -> Nat
elemAt Z     (x::xs) = x
elemAt (S n) (x::xs) = elemAt n xs
elemAt _ [] = 0

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
            Just b => elemAt b imIndex
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
permToVect1 (p::ps) allMoved = (permToVectSingle p allMoved)::(permToVect1 ps allMoved)

||| A union of all the points moved in a set of permutations
||| @p2 preimage-image instance of permutation to be converted
movedPointsInPerms : Eq s => (p2 : List (Permutation s)) -> (FiniteSet s)
movedPointsInPerms Nil = empty
movedPointsInPerms (p::ps) = union (preimage p) (movedPointsInPerms ps)

||| covert a list of preimage-image permutations to a vector type
||| @p preimage-image instance of permutation to be converted
permToVect : Eq s => (mp:(FiniteSet s)) ->
                     (p : List (Permutation s)) ->
                     PermsIndexed s fs
permToVect mp p = 
  let
    --pPreIm :(FiniteSet s) = movedPointsInPerms p
    mapping : List (List Nat) = permToVect1 p mp
  in MkPermsIndexed mapping

||| Function used locally by bsgs as first stage in
||| constructing strong generators.
||| Encodes a permutation as a 'vector', a list of indexes
||| where the first entry gives the index that point 1
||| translates to,  the second entry gives the index that
||| point 2 translates to, and so on.
||| There are 2 versions of this function. If S has
||| OrderedSet then the points are sorted so that index 1
||| is the lowest and so on.
||| Parameter definitions:
||| @i index to element (1..degree)
||| @q result so far
||| @mp   - moved points is list of elements of set
|||          which are moved by p.
||| @p      - permutation being converted.
||| @degree - number of points being permuted.
perm_to_vec : Eq set => (i : Nat) ->
              (q : (List Nat)) ->
              (mp : FiniteSet set) ->
              (p : (Permutation set)) ->
              (degree : Nat) ->
              (List Nat)
perm_to_vec i q mp p degree =
  let
    pre : FiniteSet set = preimage p
    ima : FiniteSet set = image p
    qe : Nat = FiniteSet.lookupIndexed i pre ima
  in 
    if (S i) < degree
    then perm_to_vec (S i) (qe::q) mp p degree
    else qe::q

||| convert the definition of the group in terms of a mapping between
||| abitary sets to a definition using Nat which is easier to work with.
||| @newGroup generators (permutations) calculated so far
||| @words for word problem
||| @mp   - moved points is list of elements of set which are moved.
||| @degree - number of points being permuted.
||| @ggg index
||| @ggp group input
convertToVect: Eq set => (newGroup : List (List Nat)) ->
              (words : List (List Nat)) ->
              (mp : FiniteSet set) ->
              (degree : Nat) ->
              (ggg : Nat) ->
              (ggp: List (Permutation set)) ->
              (List (List Nat) , List (List Nat) , Nat , List (Permutation set))
convertToVect newGroup words mp degree ggg Nil =
  (newGroup,words,S ggg,Nil)
convertToVect newGroup words mp degree ggg (ggp::ggps) =
  let
    -- q is current generator
    q : List Nat = perm_to_vec Z (replicate degree 0) mp ggp degree
  in (q::newGroup,words,S ggg,ggps)

||| return the n th generator
nthGen : Eq s => (g : (PermsIndexed s fs)) -> (n : Nat) -> Maybe PermIndexedElement
nthGen g n = List.index' n (gensIndexed g)

||| find the first generator g that moves point p
||| used by permgrps.bsgs1
firstMover : Eq s => (g : (PermsIndexed s fs)) -> (p : Nat) -> Maybe PermIndexedElement
firstMover g p =
  firstMover1 g p 0
    where
      firstMover1 : Eq s => (g : (PermsIndexed s fs)) ->
                           (p : Nat) ->
                           (i : Nat) ->
                           Maybe PermIndexedElement
      firstMover1 g p i =
        let
          x:Maybe PermIndexedElement =nthGen g i
        in
          case x of
            Nothing => Nothing
            Just y =>
              if p == elementAt p y
              then firstMover1 g p (S i)
              else Just y

||| modify generators so no generators stabilise i
||| used by bsgs1
||| @p initial generators
||| @x non trivial element (element that does not stabise i
||| @i point which will not be stabilised
modifyGens : (p : (PermsIndexed s fs)) -> (x:PermIndexedElement) -> (i:Nat) -> PermsIndexed s fs
modifyGens p x i =
  MkPermsIndex (modyfyGens1 (gensIndexed p) x i) where
    modyfyGens1 : (List PermIndexedElement) -> PermIndexedElement -> Nat -> (List PermIndexedElement)
    modyfyGens1 Nil x1 i1 = Nil
    modyfyGens1 (p1::ps) x1 i1 =
      --if index' i1 p1 == Just i1
      if evalv p1 i1 == i1
      then (p1 * x1)::(modyfyGens1 ps x1 i1)
      else p1::(modyfyGens1 ps x1 i1)

||| returns true if x is a generator of p
member : (p : (PermsIndexed s fs)) -> (x:PermIndexedElement) -> Bool
member p x =
  let
    gens : List PermIndexedElement = gensIndexed p
  in
    elem x gens

{-||| orbit returns the orbit of element (el) under the
||| permutation p, i.e. the set which is given by applications of
||| the powers of p to el.
||| @p permutation
||| @el element
orbit : Eq s => (p : (PermsIndexed s)) -> (el : s) -> (FiniteSet s)
orbit p el = buildOrbit p el empty
  where
    buildOrbit : Eq s => (p : (PermsIndexed s)) -> (el : s) -> (FiniteSet s) -> (FiniteSet s)
    buildOrbit p el orbBuild = 
      let el2:s = eval p el
      in if el==el2
         then orbBuild
         else buildOrbit p el2 (insert el2 orbBuild)
-}


||| Return True if maps are the same but they can
||| be reordered and still be True provided mp and map are
||| reordered in the same way.
implementation Eq (PermsIndexed s fs) where
  (==) a b = 
    --((mp a) == (mp b)) && ((perms a) == (perms b))
    ((perms a) == (perms b))


--implementation Show fs => Show PermsIndexed (fs:(FiniteSet s)) where
implementation Show (PermsIndexed s fs) where
    --show a = "permsIndexed " ++(show (mp a)) ++ (show (perms a))
    show a = "permsIndexed " ++ (show (perms a))

