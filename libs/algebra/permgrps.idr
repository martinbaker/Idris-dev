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
 - I (Martin Baker) was therefore motivated to write these notes.
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

{-
to run:

    /  _/___/ /____(_)____                                     
    / // __  / ___/ / ___/     Version 1.2.0
  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      
 /___/\__,_/_/  /_/____/       Type :? for help               

Idris is free software with ABSOLUTELY NO WARRANTY.            
For details type :warranty.
Idris> :module permgrps
*permgrps> :exec
[68, 79, 6]
*permgrps> :exec
[93, 4, 3]
*permgrps> 

-}
--module permgrp
module Main

-- For now we need to have some runtime errors. I cant work out how
-- to use Idris type system to make then impossible.
import public finiteSet
import public perm
import public Effects
import public Effect.Random
import public Effect.System

%access public export

||| holds orbit and Schreier vector
record Rec where
   constructor Record1
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
   svc : List Integer -- was V I

||| REC2 holds extra information about group in representation
||| to improve efficiency of some functions.
record Rec2 set where
   constructor Record2
   ||| order  - Number of elements. Zero means that 'information'
   ||| data has not yet been computed.
   order : Nat
   ||| sgset  - Strong Generators
   sgset : List (List Nat) -- was List V Nat
   ||| gpbase - sequence of points stabilised by the group.
   gpbase : List Nat
   ||| orbs   - Describes orbits of base point.
   orbs : List Rec -- V Rec
   ||| mp - List of elements of S moved by some permutation
   ||| (needed for mapping between permutations on S and
   |||  internal representation)
   mp : List set
   ||| wd - Gives representation of strong generators in terms
   ||| of original generators
   wd : List (List Nat)

||| This type represents the whole group, not an element of the group.
||| The 'gens' component completely defines the group as a list
||| of permutations. This is set when the group is constructed.
||| The information component allows some functions to be run
||| more efficiently this data is created, when needed from gens.
||| The parts of the information data are defined as follows:
record PermutationGroup set where
   constructor PermGrp
   ||| generators of the group
   gens:(List (Permutation set))
   ||| cached information to speed up computation.
   ||| I know its not FP style to explicity cache information but
   ||| it is important that this is calculated once because it involves
   ||| random methods.
   information:(Rec2 set)

||| REC3 holds an element and a word
record Rec3 where
   constructor Record3
   ||| element
   elt : List Nat
   ||| word
   lst : List Nat
   |||
   val : Nat

show : Rec3 -> String
show a =
  let
    s1:String = Prelude.Show.show (elt a)
    s2:String = Prelude.Show.show (lst a)
  in "Rec3:" ++ s1 ++ ":" ++ s2 ++ ":" ++ show (val a)

||| internal multiplication of permutations
||| (multiply means compose permutations)
times : ( p : List Nat) ->( q : List Nat ) -> (List Nat)
times p q =
  let
    pIn : List Nat = [1..(length p)]
  in reverse (compose pIn p q Nil)
    where
      compose : (List Nat) -> (List Nat) -> (List Nat) -> (List Nat) -> (List Nat)
      compose Nil bs cs ds = ds
      compose (Z::as) bs cs ds = (Z::ds)
      compose ((S a)::as) bs cs ds =
        let
          bm : Maybe Nat = index' a bs
          b : Nat = case bm of
            Nothing => 0
            Just Z => 0
            Just (S x) => x
          cm : Maybe Nat = index' b cs
          c : Nat = case cm of
            Nothing => 0
            Just x => x
        in
          compose as bs cs (c::ds)

||| At start of program Initialise random number generator
||| by setting seed to system time.
rndNumInit : Nat -> Eff Integer [RND, SYSTEM]
rndNumInit last = do
    srand !time
    rndInt 0 (cast last)

||| get a random number between 0 and last
rndNum : Nat -> Eff Integer [RND, SYSTEM]
rndNum last = rndInt 0 (cast last)

||| Local function used by bsgs1 to generate a "random" element.
ranelt : (group : List (List Nat)) ->
         (word : List (List Nat)) ->
         (maxLoops : Integer) ->
         Eff Rec3 [RND,SYSTEM]
ranelt group word maxLoops =
  let
    numberOfGenerators:Nat = length group
    randomInteger:Nat = cast(! (rndNum numberOfGenerators) )
    -- randomInteger is a number between 0 and number of gens -1
    randomElement : List Nat = case index' randomInteger group of
      Nothing => Nil
      Just x => x
    doWords : Bool = case word of
      Nil => False
      _ => True
    words : List Nat = case index' randomInteger word of
      Nothing => Nil
      Just x => x
    numberOfLoops : Nat =
      if maxLoops < 0
      then cast (- maxLoops)
      else cast ! (rndNum (cast maxLoops))
  in 
    mix (Record3 randomElement words randomInteger) numberOfLoops numberOfGenerators doWords
      where
        mix : Rec3 -> Nat -> Nat -> Bool -> Eff Rec3 [RND,SYSTEM]
        mix r Z n w = pure r
        mix r (S a) n w =
         let
           randomInteger2:Nat = cast ! (rndNum n) 
           -- randomInteger2 is a number between 0 and number of gens -1
           randomElement2 : List Nat = case index' randomInteger2 group of
             Nothing => Nil
             Just b => b
           randomElement3 : List Nat = times (elt r) randomElement2
           w3 : List Nat =
             if w
             then 
               let
                 words2: List Nat = case index' randomInteger2 word of 
                   Nothing => Nil
                   Just b => b
               in (lst r) ++ words2
             else (lst r)
         in mix (Record3 randomElement3 w3 randomInteger2) a n w

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
orbitWithSvc1 : (group : List (List Nat)) ->
                (grpinv : List (List Nat)) ->
                (point : Nat) -> Rec
orbitWithSvc1 group grpinv point =
  let
    fst : List Nat = case head' group of
      Nothing => Nil
      Just b => b
    degree : Nat = length fst
    orbit : List Nat = [ point ]
    orbitv : List Nat = case degree of
      Z => Nil
      (S a) => point::(replicate a 0)
    orbit_size : Nat = 1
    schreierVector : List Integer = replaceNth point (-1) (replicate degree (-2))
    position : Nat = 1
  in 
    mix3 orbit orbitv orbit_size schreierVector position
      where
        mix4 : (List Nat) -> (List Nat) -> Nat -> (List Integer) -> Nat -> Nat -> (List (List Nat)) ->
          ((List Nat),(List Nat),Nat,(List Integer),Nat)
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
          in (orbit,orbitv,orbit_size,schreierVector,position)
      
        mix3 : (List Nat) -> (List Nat) -> Nat -> (List Integer) -> Nat -> Rec
        mix3 orbit orbitv orbit_size schreierVector Z =
          Record1 orbit schreierVector
        mix3 orbit orbitv orbit_size schreierVector (S a) =
          let
            (orbit,orbitv,orbit_size,schreierVector,position) =
              mix4 orbit orbitv orbit_size schreierVector (S a) 0 grpinv
            m3:Rec = mix3 orbit orbitv orbit_size schreierVector position
          in m3
    {-
        
        while not zero? position repeat
            for i in 1..#grpinv for grv in grpinv repeat
                newPoint := qelt(orbitv, orbit_size - position + 1)
                newPoint := qelt(grv, newPoint)
                if qelt(schreierVector, newPoint) = -2 then
                    orbit                   := cons ( newPoint, orbit )
                    orbit_size := orbit_size + 1
                    orbitv(orbit_size) := newPoint
                    position                := position + 1
                    schreierVector.newPoint := i
            position := position - 1
        [reverse!(orbit), schreierVector ]
    -}

||| return a random element (permutation) from a PermutationGroup
random : Eq set => (group : (PermutationGroup set)) -> (maximalNumberOfFactors : Nat) ->
         Eff (Permutation set) [RND,SYSTEM]
random group maximalNumberOfFactors =
  let
    gp : (List (Permutation set)) = gens group
    numberOfGenerators : Nat = length gp
    randomInteger:Nat = cast(! (rndNum numberOfGenerators) )
    -- randomInteger is a number between 0 and number of gens -1
    randomElement : Permutation set = case index' randomInteger gp of
      Nothing => unit
      Just x => x
    numberOfLoops:Nat = cast(! (rndNum maximalNumberOfFactors) )
  in 
    mix2 numberOfLoops numberOfGenerators gp randomElement
      where
        mix2 : Nat -> Nat ->
               (List (Permutation set)) ->
               (Permutation set) -> Eff (Permutation set) [RND,SYSTEM]
        mix2 Z _ _ randomElement = pure randomElement
        mix2 (S a) numberOfGenerators gp randomElement =
          let
            randomInteger2:Nat = cast(! (rndNum numberOfGenerators) )
            -- randomInteger2 is a number between 0 and number of gens -1
            randomElement2 : Permutation set = case index' randomInteger2 gp of
              Nothing => unit
              Just x => x
          in mix2 a numberOfGenerators gp (randomElement * randomElement2)

randEle : Nat -> List (List Nat) -> Eff (List Nat) [RND, SYSTEM]
randEle randomInteger group = case index' randomInteger group of
     Nothing => pure Nil
     Just x => pure x

numOfLoops : Integer ->  Eff Nat [RND, SYSTEM]
numOfLoops maxLoops =
    if maxLoops < 0
    then pure (cast (- maxLoops))
    else pure (cast ! (rndNum (cast maxLoops)))


main : IO ()
main = 
  let
    group:List (List Nat) = [[2,1,3],[1,3,2]]
    word : List (List Nat) = Nil
    maxLoops : Integer = (6)
    numberOfGenerators:Nat = length group
    doWords : Bool = case word of
      Nil => False
      _ => True
  in do
    (randomInteger, randomInteger2, randomElement,words,numberOfLoops,v,v2) <- run $ do
      -- initialise random number seed from time
      rndNumInit 1
      randomInteger' <- rndNum numberOfGenerators
      randomInteger2' <- rndNum numberOfGenerators
      randomElement' <- randEle (cast randomInteger') group
      let words' : List Nat = case index' (cast randomInteger') word of
        Nothing => Nil
        Just x => x
      numberOfLoops' <- numOfLoops maxLoops
      v' <- (ranelt [[2,1,3],[1,3,2]] [[]] 6)
      v2' <- (ranelt [[2,1,3],[1,3,2]] [[2,1,3],[1,3,2]] (- 6))
      pure (randomInteger', randomInteger2', randomElement',words',numberOfLoops',v',v2')
    putStrLn ("numberOfGenerators=" ++ (show numberOfGenerators))
    putStrLn ("randomInteger=" ++ (show randomInteger))
    putStrLn ("randomInteger2=" ++ (show randomInteger2))
    putStrLn ("randomElement=" ++ (show randomElement))
    putStrLn ("doWords=" ++ (show doWords))
    putStrLn ("words=" ++ (show words))
    putStrLn ("numberOfLoops=" ++ (show numberOfLoops))
    putStrLn (show v)
    putStrLn (show v2)

