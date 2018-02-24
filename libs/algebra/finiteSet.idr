{-
 - (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 license but if there were any interest in including
 - this with Idris library then a compatible license would be acceptable.
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
 - this implementation is guaranteed to maintain the order that the
 - elements were added. This is not part of the mathematical requirements
 - but it is useful for computation.
 -
 - Should FiniteSet have its size as part of its type? That is, should
 - it be implemented like 'List' or like 'Vect'?
 - There are some functions where having the size available at compile time
 - would be useful. Also if finite sets have the same size they are isomorphic
 - and it might be an interesting idea to have such isomorphisms available at
 - compile time.
 - If we take the example of vector spaces then making vectors of different
 - number of dimensions, different types, is very useful because vector
 - addition is only valid
 - if the dimensions are the same. So it helps to have these errors 
 - detected at compile time. However, the situation is different for
 - FiniteSet because the size depends on the contents in complicated ways.
 - For instance:
 - * Duplicate removal can make the size unpredictable.
 - * Functions like 'union' and 'intersection' do not produce a result of
 -   a predicatable size.
 -
 - I did attempt to have 'size' as a type parameter here.
 - https://github.com/martinbaker/Idris-dev/blob/algebraAlt/libs/algebraAlt/finiteSet.idr
 - I had to to use complicated dependant pairs to get this to compile,
 - but it does not have the right information at runtime and I concluded
 - that this was not practical.
 -
 - Before writing this FiniteSet I did a quick search to check if there was
 - any other existing code that I could use but I did not find any.
 - 'fin' only seems to apply to numbers. The code here:
 - https://github.com/jfdm/idris-containers/blob/master/Data/AVL/Set.idr
 - is based on ballanced trees and so only works on ordered sets.
 -}

module FiniteSet

%access export

infixr 7 ::

||| FiniteSet: A container which cannot contain duplicates.
||| In general order is not significant in finite sets, however
||| this type does gaurantee that elements will be returned in
||| the same order as they were constructed in. This allows
||| versions where order is significant.
||| @ elem the type of elements
data FiniteSet : (elem : Type) -> Type where
  ||| Empty set
  Nil  : FiniteSet elem
  ||| A non-empty set of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (x : elem) -> (xs : FiniteSet elem) -> FiniteSet elem

||| Return an empty finite set.
||| I included this as an auxiliary constructor so that I can not
||| export the built in constructors. This is so that I can enforce
||| the no-duplicates rule.
empty : (Eq elem) => FiniteSet elem
empty = Nil

||| Does the set contain the given element.
contains : (Eq elem) => elem -> FiniteSet elem -> Bool
contains a [] = False
contains a (x::xs) = if a==x then True else contains a xs

||| insert an element into a set only if the set does not
||| already contain the element.
||| @e element to be added.
||| @x set to be added too.
insert : (Eq elem) => (e:elem) -> (x:FiniteSet elem) ->
                      FiniteSet elem
insert e x =
           if contains e x
           then x
           else e :: x

||| returns the size of the set.
||| The name 'order' might be confusing but it is the mathematical term.
order : FiniteSet elem -> Nat
order [] = 0
order (x::xs) = 1 + order xs

||| Construct a set that contains all elements in both of the input sets.
||| @x first input set
||| @y second input set
union : (Eq elem) => (x:FiniteSet elem) ->
                     (y:FiniteSet elem) ->
                     FiniteSet elem
union [] y = y
union x [] = x
union x y = case x of
        [] => y
        (a::as) => if contains a y
                   then union as y
                   else union as (insert a y)

||| Remove element 'e' in a FiniteSet
|||
||| @e the element to be dropped
dropElem : (Eq elem) => (e:elem) ->
                        FiniteSet elem ->
                        FiniteSet elem
dropElem e [] = []
dropElem e (x::xs) =
  if e == x
  then xs
  else let
    rst:(FiniteSet elem) = dropElem e xs
  in (x::rst)

||| Construct a set that contains the elements from the first input
||| set but not the second.
||| @set1 first input set.
||| @set2 second input set.
difference : (Eq elem) => (set1:FiniteSet elem) ->
                          (set2:FiniteSet elem) ->
                          FiniteSet elem
difference [] _ = []
difference x [] = x
difference x (ya::yas) = difference (dropElem ya x) yas

||| Construct a set that contains common elements of the input sets.
intersection : (Eq elem) => FiniteSet elem ->
                            FiniteSet elem ->
                            FiniteSet elem
intersection s1 s2 = difference s1 (difference s1 s2)

||| This is used in permutation set but its less messy
||| to put this function in FiniteSet namespace.
||| @input element to lookup
||| @preIm match element to this set
||| @im return corresponding element from this set
lookup : (Eq elem) => (input : elem) ->
                      (preIm : (FiniteSet elem)) ->
                      (im : (FiniteSet elem)) ->
                      elem
lookup inp [] _ = inp
lookup inp _ [] = inp
lookup inp (a :: as) (b :: bs) =
  if inp == a then b else lookup inp as bs

||| This is used in permutation set but its less messy
||| to put this function in FiniteSet namespace
multiLookup : Eq s =>  (FiniteSet s) -> (FiniteSet  s) -> (FiniteSet  s) -> (FiniteSet s)
multiLookup [] _ _ = empty
multiLookup (a::as) q p = insert (lookup a q p) (multiLookup as q p)

indexOf : Eq s => (FiniteSet s) -> s -> Nat -> Nat
indexOf Nil b n = n
indexOf (a::as) b n =
  if a==b
  then n
  else indexOf as b (S n)

||| Lookup Index in first set and return the index of the corresponding element
||| in the second set.
||| Only valid for cases of set where order is significant
||| This is used in permutation set but its less messy
||| to put this function in FiniteSet namespace
lookupIndexed : Eq s => (n : Nat) ->
                (preIm : FiniteSet s) ->
                (im : FiniteSet s) -> Nat
lookupIndexed Z (x::xs) y= indexOf y x 0
lookupIndexed (S n) (x::xs) y= lookupIndexed n xs y
lookupIndexed _ [] _ = 0

||| This is used in permutation set but its less messy
||| to put this function in FiniteSet namespace
dropFixpoint : Eq s => (FiniteSet s) -> (FiniteSet  s) -> ((FiniteSet  s),(FiniteSet s))
dropFixpoint [] [] = ([],[])
dropFixpoint (a::as) (b::bs) =
  if a==b
  then dropFixpoint as bs
  else
    let
      r:((FiniteSet s),(FiniteSet s)) = dropFixpoint as bs
      ras:(FiniteSet s) = fst r
      rbs:(FiniteSet s) = snd r
    in
      ((a::ras),(b::rbs))

||| Construct a list using the given set.
||| @set set to be converted to list.
toList : (set:FiniteSet elem) -> List elem
toList [] = List.Nil
toList (x::xs) = List.(::) x (toList xs)

||| Reverse the order of the elements of a FiniteSet.
||| Since order is irrelevant this does not really change the set
||| but 'reverse' is used by 'fromList' to keep the set looking
||| the same as the list.
reverse : (Eq elem) => FiniteSet elem -> FiniteSet elem
reverse xs = go [] xs
  where go : FiniteSet elem -> FiniteSet elem -> FiniteSet elem
        go acc []        = acc
        go acc (x :: xs) = go (x::acc) xs

||| does not remove duplicates - need to use 'insert' like code above
fromList' : (Eq elem) => FiniteSet elem -> (l : List elem) -> FiniteSet elem
fromList' ys [] = ys
fromList' ys (x::xs) = fromList' (insert x ys) xs

||| Convert a list to a finite set.
||| If the list contains duplicates then only one element of each
||| value will be added.
|||
||| The length of the list should be statically known.
fromList : (Eq elem) => (l : List elem) -> FiniteSet elem
fromList l = reverse $ fromList' empty l

||| order is not significant when comparing sets so equality returns true
||| if both sets contain the same elements regardless of order.
implementation (Eq elem) => Eq (FiniteSet elem) where
  (==) [] [] = True
  (==) [] _ = False
  (==) _ [] = False
  (==) a b = (order (difference a b) == 0 ) && (order (difference b a) == 0 )

||| This is a stricter version of equality test which requires both
||| parameters to have their elements in the same order. Although presevation
||| of order is not a general requirement of a finite set this type does
||| gaurantee not to change the order of the set.
identical : (Eq elem) => (FiniteSet elem) -> (FiniteSet elem) -> Bool
identical [] [] = True
identical (a::as) (b::bs) = a == b && (identical as bs)
identical _ _ = False

||| used by movedPoints in Permutation. returns the set of points moved
mPoints : Eq set => (FiniteSet set) -> (FiniteSet set) -> (FiniteSet set) -> (FiniteSet set)
mPoints FiniteSet.Nil FiniteSet.Nil c = c

mPoints (a :: as) (b :: bs) c =
  if a==b
  then mPoints as bs c
  else mPoints as bs (a::c)

mPoints _ _ c = c

{-||| Attempt to find the nth element of a set.
||| If the provided index is out of bounds, return Nothing.
||| Only valid for cases of set where order is significant
index' : (n : Nat) -> (l : FiniteSet a) -> Maybe a
index' Z     (x::xs) = Just x
index' (S n) (x::xs) = FiniteSet.index' n xs
index' _     []      = Nothing-}

implementation Show elem => Show (FiniteSet elem) where
    show = show . toList
