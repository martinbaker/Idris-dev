{-
 - (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 licence but if there were any interest in including
 - this with Idris library then a compatible licence would be acceptable.
 - 
 - This code attempts to implement quaternions using Idris.
 - For an explanation with example session see this page:
 - http://www.euclideanspace.com/prog/idris/quaternion/
 - for more general information about objectives see this page:
 - http://www.euclideanspace.com/prog/idris/
 -
 - A finite set is a set of elements with no duplicates.
 - There are no specific requirements about what the elements are
 - other than:
 - * The elements are all of a given type.
 - * We must be able to determine equality of elements, that is they
 -   must implement 'Eq'.
 -
 - There is no requirement that the elements are ordered, that is the
 - 'Ord' interface is not required.
 - Although a finite set does not need a concept of order, in general,
 - this implementation is gauranteed to maintain the order that the
 - elements were added. This is not part of the mathematical requirements
 - but it is useful for computation.
 -
 - Should FiniteSet have its size as part of its type? That is, should
 - it be implemented like 'List' or like 'Vect'? If we take the example
 - of vector spaces then making vectors of different number of dimensions,
 - different types, is very useful because vector addition is only valid
 - if the dimensions are the same. So it helps to have these errors 
 - detected at compile time. However, the situation is different for
 - FiniteSet because functions like 'union' and 'intersection' do not
 - produce a result of a predicatable size, we have to use complicated
 - dependant pairs to get this to work. But there are some functions where
 - having the size availible at compile time is useful. Also if finite sets
 - have the same size they are isomorphic and it might be an interesting
 - idea to have such isomorphisms availible at compile time. So, for now,
 - I will continue to include the size in the type.
 -
 - I therefore based this code on 'Vect'.
 - Before writing this code I did a quick search to check if there was
 - any other existing code that I could use but I did not find any.
 - 'fin' only seems to apply to numbers. The code here:
 - https://github.com/jfdm/idris-containers/blob/master/Data/AVL/Set.idr
 - is based on ballanced trees and so only works on ordered sets.
 -}

module FiniteSet

--import public Data.Fin
--import Language.Reflection

%access export

infixr 7 ::

||| FiniteSet: Similar to Vect, that is, generic lists with explicit
||| length in the type. The difference is FiniteSet cannot contain
||| duplicates.
||| @ len the length of the list
||| @ elem the type of elements
data FiniteSet : (len : Nat) -> (elem : Type) -> Type where
  ||| Empty set
  Nil  : FiniteSet Z elem
  ||| A non-empty set of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (x : elem) -> (xs : FiniteSet len elem) -> FiniteSet (S len) elem

||| Return a empty set of a given type.
empty : (elem:Type) -> FiniteSet Z elem
empty ty = Nil

||| Does the set contain the given element.
contains : (Eq elem) => elem -> FiniteSet len elem -> Bool
contains a [] = False
contains a (x::xs) = if a==x then True else contains a xs

||| insert an element into a set only if the set does not
||| already contain the element.
||| @e element to be added.
||| @x set to be added too.
insert : (Eq elem) => (e:elem) -> {len:Nat} -> (x:FiniteSet len elem) ->
                      (len2:Nat ** FiniteSet len2 elem)
insert e {len} x = 
           if contains e x
           then (len ** x)
           else ((S len) ** (e :: x))

||| I don't yet trust the static type level value for length
||| so, for now, calculate at runtime.
size : FiniteSet len elem -> Nat
size [] = 0
size (x::xs) = 1 + size xs

||| Construct a set that contains all elements in both of the input sets.
||| @x first input set
||| @y second input set
union : (Eq elem) => {lena:Nat} -> (x:FiniteSet lena elem) ->
                     {lenb:Nat} -> (y:FiniteSet lenb elem) ->
                     (len2 ** FiniteSet len2 elem)
union [] {lenb} y = (lenb ** y)
union {lena} x [] = (lena ** x)
union {lena} x {lenb} y = case x of
        [] => (lenb ** y)
        (a::as) => if contains a y
                   then union as y
                   else union as (snd (insert a y))

||| Remove element 'e' in a FiniteSet
|||
||| @e the element to be dropped
dropElem : (Eq elem) => (e:elem) ->
                        {lena:Nat} -> FiniteSet lena elem ->
                        (q ** FiniteSet q elem)
dropElem e [] = (0 ** [])
dropElem e {lena = (S lena)} (x::xs) =
  if e == x
  then (lena ** xs)
  else let
    rst:(q2 ** FiniteSet q2 elem) = dropElem e xs
  in((S (fst rst)) ** x::(snd rst))

||| Construct a set that contains the elements from the first input
||| set but not the second. This is a variant of the difference
||| function which takes a dependant pair as its first parameter.
||| @set1 first input set is dependant pair.
||| @set2 second input set.
difference' : (Eq elem) => (set1:(lena ** FiniteSet lena elem)) ->
                          {lenb:Nat} -> (set2:FiniteSet lenb elem) ->
                          (len2 ** FiniteSet len2 elem)
difference' (Z ** []) {lenb} _ = (Z ** [])
difference' x [] = x
difference' x {lenb = S lenb} (ya::yas) = difference' (dropElem ya (snd x)) yas

||| Construct a set that contains the elements from the first input
||| set but not the second.
||| @set1 first input set.
||| @set2 second input set.
difference : (Eq elem) => {lena:Nat} -> (set1:FiniteSet lena elem) ->
                          {lenb:Nat} -> (set2:FiniteSet lenb elem) ->
                          (len2 ** FiniteSet len2 elem)
difference [] {lenb} _ = (Z ** [])
difference {lena} x [] = (lena ** x)
difference {lena = S lena} x {lenb =S lenb} (ya::yas) = difference' (dropElem ya x) yas

||| Construct a set that contains common elements of the input sets.
intersection : (Eq elem) => FiniteSet lena elem ->
                            FiniteSet lenb elem ->
                            (len2 ** FiniteSet len2 elem)
intersection s1 s2 = difference s1 (snd (difference s1 s2))

||| Construct a list using the given set.
||| @set set to be converted to list.
toList : (set:FiniteSet len elem) -> List elem
toList [] = List.Nil
toList (x::xs) = List.(::) x (toList xs)

||| Reverse the order of the elements of a FiniteSet.
||| Since order is irrelavent this does not really change the set
||| but 'reverse' is used by 'fromList' to keep the set looking
||| the same as the list.
reverse : FiniteSet len elem -> FiniteSet len elem
reverse xs = go [] xs
  where go : FiniteSet n elem -> FiniteSet m elem -> FiniteSet (n+m) elem
        go {n}         acc []        = rewrite plusZeroRightNeutral n in acc
        go {n} {m=S m} acc (x :: xs) = rewrite sym $ plusSuccRightSucc n m
                                       in go (x::acc) xs

fromList' : FiniteSet len elem -> (l : List elem) -> FiniteSet (length l + len) elem
fromList' ys [] = ys
fromList' {len} ys (x::xs) =
  rewrite (plusSuccRightSucc (length xs) len) ==>
          FiniteSet (plus (length xs) (S len)) elem in
  fromList' (x::ys) xs

||| Convert a list to a finite set.
|||
||| The length of the list should be statically known.
fromList : (l : List elem) -> FiniteSet (length l) elem
fromList l =
  rewrite (sym $ plusZeroRightNeutral (length l)) in
  reverse $ fromList' [] l

||| order is not significant when comparing sets so equality returns true
||| if both sets contain the same elements regardless of order.
implementation (Eq elem) => Eq (FiniteSet len elem) where
  (==) []      []      = True
  (==) x y = (fst (difference x y) == Z ) && (fst (difference y x) == Z )

implementation Show elem => Show (FiniteSet len elem) where
    show = show . toList
