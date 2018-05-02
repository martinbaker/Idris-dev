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

||| This code implements an element of a permutation
||| in an indexed form which is easier to work with
||| than the preimage-image form.
module permIndexedElement

-- For now we need to have some runtime errors. I cant work out how
-- to use Idris type system to make then impossible.
--import Effects
import public finiteSet
import public perm
--import Effect.Exception

%access public export

||| PermIndexedElement holds an element (single permutation)
||| and a word
record PermIndexedElement where
   constructor PIE
   ||| element as single permutation
   elt : List Nat
   ||| element as a word (original generators are
   ||| single Nat)
   lst : List Nat
   ||| length of both elt and lst
   ln : Nat

implementation Show PermIndexedElement where
  show a =
    let
      s1:String = Prelude.Show.show (elt a)
      s2:String = Prelude.Show.show (lst a)
    in "PIE:" ++ s1 ++ ":" ++ s2 ++ ":" ++ show (ln a)

||| elements are the same if permutations are the same
implementation Eq PermIndexedElement where
  (==) p q =
    let
      p1:List Nat = elt p
      q1:List Nat = elt q
    in p1==q1

||| eval returns the image of element (el) under the
||| permutation p.
||| @p single permutation as a list of indexes
||| @el element index to be evaluated
evalv : (p : PermIndexedElement) -> (el : Nat) -> Nat
evalv p el =
  let
    p1:List Nat = elt p
  in
    case List.index' el p1 of
      Nothing => el
      Just x => x


||| Multiplcation of permutations represents composition.
||| That is the result is the same a taking the first permutation
||| and applying the second permutation to the result of the first.
(*) : PermIndexedElement -> PermIndexedElement -> PermIndexedElement
(*) q1 p1 =
  let
    q:List Nat = elt q1
    qw:List Nat = lst q1
    pw:List Nat = lst p1
    l:Nat = ln q1
  in
    PIE (compose q p1) (qw++pw) l
      where
        compose : (List Nat) -> PermIndexedElement -> (List Nat)
        compose Nil _ = Nil
        compose (q::qs) p1 = (evalv p1 q)::(compose qs p1)

||| Attempt to find the nth element of a set.
||| If the provided index is out of bounds, return Nothing.
||| Only valid for cases of set where order is significant
elementAt : (n : Nat) -> (p : PermIndexedElement) -> Nat
elementAt n p = elementAt' n (elt p)  where
  elementAt' : (n : Nat) -> (l : List Nat) -> Nat
  elementAt' Z     (x::xs) = x
  elementAt' (S n) (x::xs) = elementAt' n xs
  elementAt' _ [] = 0

length : (p : PermIndexedElement) -> Nat
length p = length (elt p)

||| local function for invert
||| @e element to be inverted
invertEle : (e:PermIndexedElement) -> PermIndexedElement
invertEle e =
  let
    l:Nat = length e
    ew:List Nat = lst e
  in
    PIE (invertInd Z e Nil) (reverse ew) l
      where
        invertInd : Nat -> PermIndexedElement -> (List Nat) -> (List Nat)
        invertInd i v soFar =
          if (length soFar) == (length v)
          then soFar
          else invertInd (S i) v ((elementAt i v)::soFar)
