{-
 - (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 licence but if there were any interest in including
 - this with Idris library then a compatible licence would be acceptable.
 - 
 - This code implements Cycles using Idris. A cycle is like a list but has
 - no repations and loops back.
 - A set of cycles is an efficient way to notate a permutation and a set of
 - permutations can be used to define a group.
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

module cycle

%access public export

infixr 7 ::

||| Cycle, like a list but no repations and loops back.
||| A set of cycles is an efficient way to notate a permutation.
||| @ elem the type of elements
data Cycle : (elem : Type) -> Type where
  ||| Empty cycle
  Nil  : Cycle elem
  ||| A non-empty cycle of length `S len`, consisting of a head element and
  ||| the rest of the cycle, of length `len`.
  (::) : (x : elem) -> (xs : Cycle elem) -> Cycle elem

||| Return an empty cycle.
||| I included this as an auxiliary constructor so that I can not
||| export the built in constructors. This is so that I can enforce
||| the no-duplicates rule.
empty : (Eq elem) => Cycle elem
empty = Nil

||| Does the cycle contain the given element.
contains : (Eq elem) => elem -> Cycle elem -> Bool
contains a [] = False
contains a (x::xs) = if a==x then True else contains a xs

||| insert an element into a cycle only if the cycle does not
||| already contain the element.
||| @e element to be added.
||| @x cycle to be added too.
insert : (Eq elem) => (e:elem) -> (x:Cycle elem) ->
                      Cycle elem
insert e x =
           if contains e x
           then x
           else e :: x

||| returns the size of the cycle.
||| The name 'order' might be confusing but it is the mathematical term.
order : Cycle elem -> Nat
order [] = 0
order (x::xs) = 1 + order xs

||| Construct a list using the given cycle.
||| @set cycle to be converted to list.
toList : (set:Cycle elem) -> List elem
toList [] = List.Nil
toList (x::xs) = List.(::) x (toList xs)

||| Construct a list of lists from a list of cycles.
cyclesToLL : List (Cycle elem) -> List (List elem)
cyclesToLL [] = List.Nil
cyclesToLL (x::xs) = List.(::) (toList x) (cyclesToLL xs)

||| Return all elements in a set of cycles.
||| Similar to cyclesToLL but flatten into one list.
cyclesAllElements : List (Cycle elem) -> List elem
cyclesAllElements [] = List.Nil
cyclesAllElements (x::xs) = (toList x) ++ (cyclesAllElements xs)

||| local function used by cycleToPreImImage to track the first
||| element so that we can loop back to it at the end.
||| @c cycle to be converted
||| @first first element
cycleToPreImImage' : (c : Cycle elem) -> (first : elem) -> ((List elem),(List elem))
cycleToPreImImage' [] first = (first::[],first::[]) -- fixpoint
cycleToPreImImage' (x::[]) first = (x::[],first::[]) -- loop back to first
cycleToPreImImage' (x::(y::ys)) first =
  let
    (preim,im) = cycleToPreImImage' (y::ys) first
  in (x::preim,y::im)

||| Construct a PreImage-Image from a cycle.
cycleToPreImImage : Cycle elem -> ((List elem),(List elem))
cycleToPreImImage [] = (List.Nil,List.Nil)
cycleToPreImImage (x::[]) = (x::[],x::[]) -- fixpoint
cycleToPreImImage (x::(y::ys)) =
  let
    (preim,im) = cycleToPreImImage' (y::ys) x
  in (x::preim,y::im)

||| Construct a PreImage-Image from a List of cycles.
||| used to change representation of a permutation.
cyclesToPreImImage : List (Cycle elem) -> ((List elem),(List elem))
cyclesToPreImImage [] = (List.Nil,List.Nil)
cyclesToPreImImage (x::xs) =
  let
    (preim1,im1) : ((List elem),(List elem)) = cycleToPreImImage x
    (preim2,im2) : ((List elem),(List elem)) = cyclesToPreImImage xs
  in (preim1 ++ preim2 ,im1 ++ im2)

||| Reverse the order of the elements of a FiniteSet.
||| Since order is irrelevant this does not really change the set
||| but 'reverse' is used by 'fromList' to keep the set looking
||| the same as the list.
reverse : (Eq elem) => Cycle elem -> Cycle elem
reverse xs = go [] xs
  where go : Cycle elem -> Cycle elem -> Cycle elem
        go acc []        = acc
        go acc (x :: xs) = go (x::acc) xs

||| does not remove duplicates - need to use 'insert' like code above
fromList' : (Eq elem) => Cycle elem -> (l : List elem) -> Cycle elem
fromList' ys [] = ys
fromList' ys (x::xs) = fromList' (insert x ys) xs

||| Convert a list to a cycle.
||| If the list contains duplicates then only one element of each
||| value will be added.
fromList : (Eq elem) => (l : List elem) -> Cycle elem
fromList l = reverse $ fromList' empty l

||| Convert a list of lists to a list of cycles.
cyclesFromLL : (Eq elem) => (l : List (List elem)) -> List (Cycle elem)
cyclesFromLL [] = List.Nil
cyclesFromLL (x::xs) = List.(::) (fromList x) (cyclesFromLL xs)

||| Convert a list of cycles to a preImage-image.
||| Assumes that each element is only in one preimage and image
||| I can't think of a way for the type system to enforce that.
cyclesFromPreimImage : (Eq elem) => (preim : (List elem)) ->
                                   (im : (List elem)) ->
                                   List (Cycle elem)
cyclesFromPreimImage [] [] = List.Nil
cyclesFromPreimImage (x::xs) (y::ys) =
  let
    pre : elem = x
    ima : elem = y
    cyc : Cycle elem = fromList [x,y]
  in [cyc]

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

{-
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
-}

{-
||| cycles coerces a list list of cycles lls
||| to a permutation, each cycle being a list with not
||| repetitions, is coerced to the permutation, which maps
||| ls.i to ls.i+1, indices modulo the length of the list,
||| then these permutations are mutiplied.
||| Error: if repetitions occur in one cycle.
cycles : Ord s => List(List s)  -> Permutation s
cycles lls =
  unit
-}

||| Two cycles are equal if each corresponding element is equal, the
||| elements can be rotated round and the cycles are still considered
||| equal.
implementation (Eq elem) => Eq (Cycle elem) where
  (==) [] [] = True
  (==) [] _ = False
  (==) _ [] = False
  (==) (a::as) (b::bs) = a == b && (as == bs)

implementation Show elem => Show (Cycle elem) where
    show = show . toList
