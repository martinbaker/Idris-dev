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
 - elements wer added. This is not part of the mathematical requirements
 - but it is useful for computation.
 -
 - Before writing this code I did a quick search to 
 - https://github.com/jfdm/idris-containers/blob/master/Data/AVL/Set.idr
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

||| I don't yet trust the static type level value for length
||| so, for now, calculate at runtime.
size : FiniteSet len elem -> Nat
size [] = 0
size (x::xs) = 1 + size xs

insert : (Eq elem) => elem -> {len:Nat} -> FiniteSet len elem ->
                      (len2:Nat ** FiniteSet len2 elem)
insert e {len} x = 
           if contains e x
           then (len ** x)
           else ((S len) ** (e :: x))

||| Construct a set that contains all elements in both of the input sets.
union : (Eq elem) => {lena:Nat} -> FiniteSet lena elem ->
                     {lenb:Nat} -> FiniteSet lenb elem ->
                     (len2 ** FiniteSet len2 elem)
union [] {lenb} x = (lenb ** x)
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
||| set but not the second.
difference : (Eq elem) => {lena:Nat} -> FiniteSet lena elem ->
                          {lenb:Nat} -> FiniteSet lenb elem ->
                          (len2 ** FiniteSet len2 elem)
difference [] {lenb} x = (Z ** [])
difference {lena} x [] = (lena ** x)
difference {lena} x {lenb} y = case y of
    [] => (Z ** [])
    (ya::yas) => if contains ya x
                 then 
                   difference yas (snd (dropElem ya x))
                 else
                   let rst:(q2 ** FiniteSet q2 elem) = difference yas x
                   --in ((fst rst) ** (snd rst))
                   in ((S (fst rst)) ** ya::(snd rst))

||| Construct a set that contains common elements of the input sets.
intersection : (Eq elem) => FiniteSet len elem ->
                            FiniteSet len elem ->
                            (len2 ** FiniteSet len2 elem)
intersection s1 s2 = difference s1 (snd (difference s1 s2))

||| Construct a list using the given set.
toList : FiniteSet len elem -> List elem
toList [] = List.Nil
toList (x::xs) = List.(::) x (toList xs)

||| Reverse the order of the elements of a FiniteSet
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

implementation (Eq elem) => Eq (FiniteSet len elem) where
  (==) []      []      = True
  (==) (x::xs) (y::ys) = x == y && xs == ys


implementation Show elem => Show (FiniteSet len elem) where
    show = show . toList

--
-- Local Variables:
-- idris-load-packages: ("algebra.ipkg")
-- End:
