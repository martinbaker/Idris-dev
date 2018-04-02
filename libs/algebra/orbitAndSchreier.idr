{-
 - (c) 2018 Copyright Martin Baker
 - I would prefer GPL3 licence but if there were any interest in including
 - this with Idris library then a compatible licence would be acceptable.
 -
 - This type represents a permutation group.
 - The concepts come from a CAS program called Axiom and its fork FriCAS.
 - https://github.com/fricas/fricas/blob/master/src/algebra/permgrps.spad
 -
 - FriCAS is a wonderful programs but its documentation is, how can I put
 - this politely, not very good.
 - The original authors provided minimal documentation apart from a
 - reference to a paper:- C. Sims: Determining the conjugacy classes of a permutation group,
 - in Computers in Algebra and Number Theory, SIAM-AMS Proc., Vol. 4,
 - Amer. Math. Soc., Providence, R. I., 1971, pp. 191-195
 - (I can't find this paper online)
 -
 - I did find some other sources for information about the
 - Schreier-Sims algorithm such as this:
 - \url{https://en.wikipedia.org/wiki/Schreier%E2%80%93Sims_algorithm}
 -
 - Waldek Hebisch referred to these notes by A. Hulpke which contain a
 - sketch of the algorithm.
 - \url{http://www.math.colostate.edu/~hulpke/CGT/cgtnotes.pdf}
 -
 - Waldeks description on FriCAS forum here:
 - \url{https://groups.google.com/forum/?hl=en#!topic/fricas-devel/EtLwgd2dWNU}
 - 
 - I have therefore put together this together with what I have worked
 - out myself to attempt this overview of PermutationGroup code to
 - add some documentation and comments here.
 -
 - I find it improves the documentation to use diagrams, I have
 - therefore put this enhanced documentation on the web page here:
 - \url{http://www.euclideanspace.com/prog/scratchpad/mycode/discrete/finiteGroup/}
 -}

||| To do this we need to represent the group in a way that does not
||| need to compute or store all the possible elements of the group,
||| yet still be able to calculate:
||| * The order of the group.
||| * Test permutations to check if they are elements of the group.
||| * Express elements as words in the group.
||| To do this we use the theory of stabiliser chains and Schreier's
||| subgroup lemma. This requires us to compute 'base and strong
||| generators'
||| 
||| Acording to wikipedia permutation group software developed by Sims
||| led to the proof of existence of some finite simple sporadic groups
||| such as Higman–Sims, Lyons and O'Nan groups.
||| 
||| I find it easier to discuss this theory using diagrams so I have put
||| this enhanced documentation on the web page here:
||| http://www.euclideanspace.com/prog/scratchpad/mycode/discrete/finiteGroup/
module orbitAndSchreier

-- For now we need to have some runtime errors. I cant work out how
-- to use Idris type system to make then impossible.
import public finiteSet
import public perm
import public permsIndexed
import public Effects
import public Effect.Random
import public Effect.System

%access public export

||| holds orbit and Schreier vector
||| It is used for an algorithm derived from Schreier's subgroup lemma.
||| https://en.wikipedia.org/wiki/Schreier%E2%80%93Sims_algorithm
record OrbitAndSchreier set (x:(FiniteSet set)) where
   constructor MkOrbSch
   ||| a list of points on the orbit.
   orb : List Nat
   ||| The Schreier vector (svc) part allows you to compute element
   ||| of the group moving given point to base point of the orbit.
   ||| *  -2 means point not in orbit,
   ||| *  -1 means base point,
   ||| positive value is index of strong generator moving
   ||| given point closer to base point.
   ||| This list of orbits tends to be in a certain order,
   ||| (corresponding to the order of gpbase)that is, stabiliser of
   ||| point 1 (if it exists) is first then the other stabilisers,
   ||| then the final orbit may not stabilise any points.
   svc : List Int

||| replace the n th term in a list with given value
||| If nth term does not exist then don't do anything so no
||| need for error checking.
replaceNth : Nat -> v -> List v -> List v
replaceNth n newVal Nil = Nil
replaceNth n newVal (x::xs) =
  case n of
    Z => newVal::xs
    (S a) => x::(replaceNth a newVal xs)

||| Local function used by orbitWithSvc which is used by bsgs1
||| Given a set of generators and a point this calculates the
||| orbit and schreierVector.
||| That is the points that can reach given point and the index
||| of the generators used.
||| For Schreier vector (denoted svc),
|||    "-2" means not in the orbit,
|||    "-1" means starting point,
|||    PI correspond to generators
||| @group    holds permutations as vectors as they are easier to
|||           work with.
||| @grpinv inverse of group (all generators reversed).
orbitWithSvc1 : (Eq set) => (group :(PermsIndexed set fs)) ->
               (grpinv :(PermsIndexed set fs)) ->
               (point : Nat) -> (OrbitAndSchreier set fs)
orbitWithSvc1 group grpinv point =
  let
    fst : List Nat = case head' (perms group) of
      Nothing => Nil
      Just b => b
    degree : Nat = length fst
    orbit : List Nat = [ point ]
    orbitv : List Nat = case degree of
      Z => Nil
      (S a) => point::(replicate a 0)
    orbit_size : Nat = 1
    schreierVector : List Int = replaceNth point (-1) (replicate degree (-2))
    position : Nat = 1
  in 
    mix3 orbit orbitv orbit_size schreierVector position
      where
        mix4 : (List Nat) -> -- orbit
               (List Nat) -> -- orbitv
               Nat ->        -- orbit size
               (List Int) -> -- schreierVector
               Nat ->        -- position
               Nat ->        -- i - index of current permutation
               (List (List Nat)) -> -- remaining inverse permutations
               ((List Nat),(List Nat),Nat,(List Int),Nat)
        mix4 orbit orbitv orbit_size schreierVector position i Nil=
          (orbit,orbitv,orbit_size,schreierVector,position)
        mix4 orbit orbitv orbit_size schreierVector position i (grv::gs)=
          let
            ptr : Nat = minus orbit_size position
            newPoint : Nat = case index' ptr orbitv of
              Nothing => 0
              Just b => b
            -- newPoint set to current point
            newPoint2 : Nat = case index' newPoint grv of
              Nothing => 0
              Just b => b
            -- newPoint set to preimage of current point
            newPoint3 : Int = case index' newPoint2 schreierVector of
              Nothing => 0
              Just b => b
            -- -2 means preimage has not yet been reached so add it to orbit
            orbit2:(List Nat) = if newPoint3 == (-2) then newPoint2::orbit else orbit
            orbit_size2:Nat = if newPoint3 == (-2) then S orbit_size else orbit_size
            orbitv2:(List Nat) =
              if newPoint3 == (-2)
              then replaceNth orbit_size newPoint2 orbitv
              else orbitv
            position2:Nat = if newPoint3 == (-2) then S position else position
            schreierVector2:(List Int) =
              if newPoint3 == (-2)
              then replaceNth newPoint2 (cast i) schreierVector
              else schreierVector
          in (mix4 orbit2 orbitv2 orbit_size2 schreierVector2 position2 (S i) gs)
      
        mix3 : (List Nat) -> -- orbit initialised to: [point=x where x=0,1,2]
               (List Nat) -> -- orbitv initialised to: [point,0,0]
               Nat ->        -- orbit size initialised to 1
               (List Int) -> -- schreierVector initialised to: [-1,-2,-2] [-2,-1,-2] and so on
               Nat ->        -- position initialised to 1
               (OrbitAndSchreier set fs)
        mix3 orbit orbitv orbit_size schreierVector Z =
          MkOrbSch (reverse orbit) schreierVector
        mix3 orbit orbitv orbit_size schreierVector (S a) =
          let
            (orbit,orbitv,orbit_size,schreierVector,position) =
              mix4 orbit orbitv orbit_size schreierVector (S a) 0 (perms grpinv)
          in 
            case position of
              Z => MkOrbSch (reverse orbit) schreierVector
              (S p) => mix3 orbit orbitv orbit_size schreierVector p

||| Local function used by bsgs1
||| Given a group and a point in the group this calculates the
||| orbit and schreierVector.
||| Calculates inverse group, then orbitWithSvc1 does the work.
||| It is hard to describe these functions without diagrams so
||| I have put a better explanation here:
||| http://www.euclideanspace.com/prog/scratchpad/mycode/discrete/finiteGroup/index.htm#orbitWithSvc
||| @group    holds permutations as vectors as they are easier to
|||           work with.
orbitWithSvc : (Eq set) => (group :(PermsIndexed set fs)) ->
               (point : Nat) ->
               (OrbitAndSchreier set fs)
orbitWithSvc group point =
  orbitWithSvc1 group (invert group) point

||| Return True if maps are the same but they can
||| be reordered and still be True provided mp and map are
||| reordered in the same way.
implementation Eq (OrbitAndSchreier s fs) where
  (==) a b = 
    ((orb a) == (orb b)) && ((svc a) == (svc b))

implementation Show (OrbitAndSchreier s fs) where
    show a = 
      "orbit&Schreier orb=" ++ (show (orb a)) ++
      " svc=" ++ (show (svc a))

------------------------ test code ----------------------------------
orbitWithSvc1Test : (Eq set) => (group :(PermsIndexed set fs)) ->
               (grpinv :(PermsIndexed set fs)) ->
               (point : Nat) ->
               ((List Nat),(List Nat),Nat,(List Int),Nat)
orbitWithSvc1Test group grpinv point =
  let
    fst : List Nat = case head' (perms group) of
      Nothing => Nil
      Just b => b
    degree : Nat = length fst
    orbit : List Nat = [ point ]
    orbitv : List Nat = case degree of
      Z => Nil
      (S a) => point::(replicate a 0)
    orbit_size : Nat = 1
    schreierVector : List Int = replaceNth point (-1) (replicate degree (-2))
    position : Nat = 1
  in 
    (mix4 orbit orbitv orbit_size schreierVector position 0 (perms grpinv))
      where
        mix4 : (List Nat) ->
               (List Nat) ->
               Nat ->
               (List Int) ->
               Nat -> Nat ->
               (List (List Nat)) ->
               ((List Nat),(List Nat),Nat,(List Int),Nat)
        mix4 orbit orbitv orbit_size schreierVector position i Nil=
          (orbit,orbitv,orbit_size,schreierVector,position)
        mix4 orbit orbitv orbit_size schreierVector position i (grv::gs)=
          let
            ptr : Nat = minus orbit_size position
            newPoint : Nat = case index' ptr orbitv of
              Nothing => 0
              Just b => b
            newPoint2 : Nat = case index' newPoint grv of
              Nothing => 0
              Just b => b
            newPoint3 : Int = case index' newPoint2 schreierVector of
              Nothing => 0
              Just b => b
            orbit2:(List Nat) = if newPoint3 == (-2) then newPoint2::orbit else orbit
            orbit_size2:Nat = if newPoint3 == (-2) then S orbit_size else orbit_size
            orbitv2:(List Nat) =
              if newPoint3 == (-2)
              then replaceNth orbit_size newPoint2 orbitv
              else orbitv
            position2:Nat = if newPoint3 == (-2) then S position else position
            schreierVector2:(List Int) =
              if newPoint3 == (-2)
              then replaceNth newPoint2 (cast i) schreierVector
              else schreierVector
          in (mix4 orbit2 orbitv2 orbit_size2 schreierVector2 position2 (S i) gs)

orbitWithSvcTest : (Eq set) => (group :(PermsIndexed set fs)) ->
               (point : Nat) ->
               ((List Nat),(List Nat),Nat,(List Int),Nat)
orbitWithSvcTest group point =
  orbitWithSvc1Test group (invert group) point

-- orbit initialised to: [point=x where x=0,1,2]
-- orbitv initialised to: [point,0,0]
-- orbit size initialised to 1
-- schreierVector initialised to: [-1,-2,-2] [-2,-1,-2] and so on
-- position initialised to 1
 
--orb for pt0 in d3 group ([1, 0], ([0, 1, 0], (2, ([-1, 0, -2], 2))))
--orb for pt1 in d3 group ([2, 0, 1], ([1, 0, 2], (3, ([0, -1, 1], 3))))
--orb for pt2 in d3 group ([0, 2], ([2, 0, 0], (2, ([1, -2, -1], 2))))



