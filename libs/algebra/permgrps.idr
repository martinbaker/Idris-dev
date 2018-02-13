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
--import Effects
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

show : Rec3 -> String
show a =
  let
    s1:String = Prelude.Show.show (elt a)
    s2:String = Prelude.Show.show (lst a)
  in "Rec3:" ++ s1 ++ ":" ++ s2

||| internal multiplication of permutations
||| (multiply means compose permutations)
times : ( p : List Nat) ->( q : List Nat ) -> (List Nat)
times p q =
  p
{-        degree := #p
        res : V NNI := new(degree, 0)
        times!(res, p, q)
        res
-}

rndList : Eff (List Integer) [RND, SYSTEM]
rndList = do
    srand !time
    mapE (\x => rndInt 0 x) $ List.replicate 3 100

rndNum : Nat -> Eff Integer [RND, SYSTEM]
rndNum last = do
    srand !time
    rndInt 0 (cast last)

||| Local function used by bsgs1 to generate a "random" element.
ranelt : (group : List (List Nat)) ->
         (word : List (List Nat)) ->
         (maxLoops : Nat) ->
         Eff Rec3 [RND,SYSTEM]
ranelt group word maxLoops =
  let
    numberOfGenerators:Nat = length group
    randomInteger:Nat = cast ! (rndNum numberOfGenerators)
    randomElementM : Maybe (List Nat) = index' randomInteger group
    randomElement : List Nat = case randomElementM of
      Nothing => Nil
      Just x => x
    --t:Eff Integer [SYSTEM] = time
    --t' <- t
    --seed:Eff () [RND] = srand 1
    --rnd:Eff Integer [RND] = rndInt 0 100
    --  do 
    --    -- t <- time
    --    -- srand t
    --    pure (rndInt 0 100)
  in 
    pure (Record3 randomElement randomElement)
    

{-        -- generate a "random" element
        numberOfGenerators    := # group
        randomInteger : I     := 1 + random(numberOfGenerators)$Integer
        randomElement : V NNI := group.randomInteger
        words                 := []$(L NNI)
        do_words : Boolean := not(empty?(word))
        if do_words then words := word.(randomInteger::NNI)
        if maxLoops > 0 then
            numberOfLoops : I  := 1 + random(maxLoops)$Integer
        else
            numberOfLoops : I := maxLoops
        while numberOfLoops > 0 repeat
            randomInteger : I := 1 + random(numberOfGenerators)$Integer
            randomElement := times(group.randomInteger, randomElement)
            if do_words then words := append(word.(randomInteger::NNI), words)
            numberOfLoops := numberOfLoops - 1
        [randomElement, words]
-}
{-
    random(group, maximalNumberOfFactors) ==
        maximalNumberOfFactors < 1 => 1$(PERM S)
        gp : L PERM S := group.gens
        numberOfGenerators := # gp
        randomInteger : I  := 1 + random(numberOfGenerators)$Integer
        randomElement      := gp.randomInteger
        numberOfLoops : I  := 1 + random(maximalNumberOfFactors)$Integer
        while numberOfLoops > 0 repeat
            randomInteger : I  := 1 + random(numberOfGenerators)$Integer
            randomElement := gp.randomInteger * randomElement
            numberOfLoops := numberOfLoops - 1
        randomElement

    random(group) == random(group, 20)

-}

main : IO ()
main = do
  --v <- run rndList
  v <- run (ranelt [[1,2,3],[4,5,6],[3,4,5]] [[1,2,3],[4,5,6],[3,4,5]] 6)
  putStrLn (show v)


