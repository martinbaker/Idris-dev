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
import public permVec
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

implementation Show Rec where
    show a = 
      "orbit&SchreiergroupInfo orb=" ++ (show (orb a)) ++
      " svc=" ++ (show (svc a))

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
   {-||| mp - moved points
   ||| Set of elements of S moved by some permutation.
   ||| That is, all points in generators, but don't
   ||| include if all generators map the points to themselves.
   ||| (needed for mapping between permutations on S and
   |||  internal representation)
   mp : FiniteSet set-}
   ||| wd - Gives representation of strong generators in terms
   ||| of original generators
   wd : List (List Nat)
   ||| temporary value for debugging only
   ||| newGroup holds permutations as vectors as they are
   ||| easier to work with.
   vecRep : PermutationVec set

implementation Show set => Show (Rec2 set) where
    show a = 
      "groupInfo order=" ++ (show (order a)) ++
      " sgset=" ++ (show (sgset a)) ++
      " gpbase=" ++ (show (gpbase a)) ++
      " orbs=" ++ (show (orbs a)) ++
      " wd=" ++ (show (wd a)) ++ "\n" ++
      " vecRep=" ++ (show (vecRep a))

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
          bm : Maybe Nat = List.index' a bs
          b : Nat = case bm of
            Nothing => 0
            Just Z => 0
            Just (S x) => x
          cm : Maybe Nat = List.index' b cs
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
    randomElement : List Nat = case List.index' randomInteger group of
      Nothing => Nil
      Just x => x
    doWords : Bool = case word of
      Nil => False
      _ => True
    words : List Nat = case List.index' randomInteger word of
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
            newPoint3 : Integer = case index' newPoint2 schreierVector of
              Nothing => 0
              Just b => b
            orbit2:(List Nat) = if newPoint3 == (-2) then newPoint2::orbit else orbit
            orbit_size2:Nat = if newPoint3 == (-2) then S orbit_size else orbit_size
            orbitv2:(List Nat) =
              if newPoint3 == (-2)
              then replaceNth orbit_size newPoint2 orbitv
              else orbitv
            position2:Nat = if newPoint3 == (-2) then S position else position
            schreierVector2:(List Integer) =
              if newPoint3 == (-2)
              then replaceNth newPoint2 (cast i) schreierVector
              else schreierVector
          in (mix4 orbit2 orbitv2 orbit_size2 schreierVector2 position2 (S i) gs)
      
        mix3 : (List Nat) -> (List Nat) -> Nat -> (List Integer) -> Nat -> Rec
        mix3 orbit orbitv orbit_size schreierVector Z =
          Record1 (reverse orbit) schreierVector
        mix3 orbit orbitv orbit_size schreierVector (S a) =
          let
            (orbit,orbitv,orbit_size,schreierVector,position) =
              mix4 orbit orbitv orbit_size schreierVector (S a) 0 grpinv
            m3:Rec = mix3 orbit orbitv orbit_size schreierVector position
          in m3

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

{-
    if S has OrderedSet then
        -- return list of points and also put into information.mp
        pointList(group : %) : L S ==
            not(empty?(group.information.mp)) => group.information.mp
            support : L S := []
            for perm in group.gens repeat
                support := merge(sort((listRepresentation perm).preimage),
                                 support)
            res :  L S := []
            empty?(support) => res
            p0 := first(support)
            res := [p0]
            for p in rest(support) repeat
                p = p0 => "iterate"
                p0 := p
                res := cons(p, res)
            group.information.mp := reverse!(res)
    else
-}

||| return list of points that are moved to put into information.mp
pointList : (Eq set) => (group : (List (Permutation set))) ->
            FiniteSet set ->
            FiniteSet set
pointList Nil a = a
pointList (g::gs) a =
  let
    newMoved : (FiniteSet set) = movedPoints g
    totalMoved : (FiniteSet set) = union newMoved a
  in pointList gs totalMoved

randEle : Nat -> List (List Nat) -> Eff (List Nat) [RND, SYSTEM]
randEle randomInteger group = case index' randomInteger group of
     Nothing => pure Nil
     Just x => pure x

numOfLoops : Integer ->  Eff Nat [RND, SYSTEM]
numOfLoops maxLoops =
    if maxLoops < 0
    then pure (cast (- maxLoops))
    else pure (cast ! (rndNum (cast maxLoops)))

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

{-        for ggg in 1..#gp for ggp in gp repeat
            q := perm_to_vec(supp, ggp, degree)
            newGroup := cons(q, newGroup )
            if wordProblem then words := cons(list ggg, words)
-}

||| This is a local function to initialise base and strong
||| generators and other values in group:%.
||| Functions such as initializeGroupForWordProblem or
||| knownGroup? are called to make sure 'information' has been
||| initialised in group:%. If initialisation is required then bsgs
||| is called to do the work.
||| Note: this function calls bsgs1 which uses Monte Carlo methods
||| (random sampling) and so may not give the same result for given
||| parameters.
||| returns sizeOfGroup but real purpose is side effects of
||| setting 'information' in group:%.
||| parameters are:
|||   group       is this instance.
|||   wordProblem is true if we want to initialise for wordProblem.
|||   maxLoops    if zero then calculate from the (approximate)
|||               base length
|||   diff        if word problem then subtract this from maxLoops.
||| It is hard to describe these functions without diagrams so
||| I have put a better explanation here:
||| http://www.euclideanspace.com/prog/scratchpad/mycode/discrete/finiteGroup/index.htm#bsgs
bsgs : (Eq set) => (group : (List (Permutation set))) ->
       (wordProblem : Bool) ->
       (maxLoops : Nat) ->
       (diff : Integer) ->
       (Rec2 set)
bsgs group wordProblem maxLoops diff =
  let
    basePoint : Nat = 0
    newBasePoint : Bool = False
    baseOfGroup : List Nat = Nil
    out : List (List (List Nat)) = Nil
    -- out will hold stabiliser chain
    outword : List (List (List Nat)) = Nil
    --outr : Reference(L L V NNI) := ref([])
    -- outr is reference to stabiliser chain (out above)
    outwordr : List (List (List Nat)) = Nil
    -- put list of points into supp and also put into
    -- information.mp
    -- mp was supp
    mp : FiniteSet set = pointList group FiniteSet.empty
    degree : Nat = order mp
  in
    if degree == 0
    then Record2 1 Nil Nil Nil Nil unitv
    else
      let
        --tmpv : List Nat = replicate degree 0
        --gp : (List (Permutation set)) = group
        --
        sgset : List (List Nat) = Nil
        gpbase : List Nat = Nil
        orbs : List Rec = Nil
        wd : List (List Nat) = Nil
        -- 'newGroup' holds permutations as vectors as they are
        -- easier to work with.
        --(newGroup,words,_,_) : (List (List Nat),List (List Nat),Nat,(List (Permutation set))) =
        -- params are: newGroup words mp degree ggg ggp
        --  convertToVect Nil Nil mp degree 0 group
        newGroup : PermutationVec set = permToVect group
      in
        Record2 degree sgset gpbase orbs wd newGroup

{-        -- If bsgs1 has not yet been called first call it with base
        -- length of 20 then call it again with more accurate base
        -- length.
        if maxLoops < 1 then
            -- try to get the (approximate) base length by pre-calling
            -- bsgs1 with maxloops=20
            if zero? (# ((group.information).gpbase)) then
                k := bsgs1(newGroup, 1, []$(L L NNI), 20, group, 0,
                                 outr, outwordr)
            maxLoops := #((group.information).gpbase) - 1
        k := bsgs1(newGroup, 1, words, maxLoops, group, diff, outr, outwordr)
        -- bsgs1 tries to get a good approximation for the base
        -- points which are put in (group.information).gpbase and
        -- stabiliser chain which is returned in 'out' parameter
        -- reference.
        -- These values can be used here to compute the strong
        -- generators but this output may contain duplicates and so
        -- we must remove these.
        out := deref(outr)
        outword := deref(outwordr)
        kkk : I := 1
        newGroup := reverse newGroup
        noAnswer : B := true
        z : V NNI
        add_cnt : I := 0
        wordlist : L L NNI
        dummy_rec : REC := [[], empty()]
        baseOfGroup := (group.information).gpbase
        gp_info.gpbase := baseOfGroup
        orbv : V REC := new(# baseOfGroup, dummy_rec)$(V REC)
        while noAnswer repeat
            gp_info.gpbase := baseOfGroup
            gp_info.orbs := orbv
            -- test whether we have a base and a strong generating set
            sgs : L V NNI := []
            wordlist := []
            for i in 1..(kkk-1) repeat
                sgs := append(sgs, out.i)
                if wordProblem then wordlist := append (wordlist, outword.i)
            noresult : B := true
            z := new(degree, 0)
            for i in kkk..#baseOfGroup while noresult repeat
                rejects := reduceGenerators(i, wordProblem, gp_info,
                                            out, outword)
                sgs := append(sgs, out.i)
                sgsv := vector(sgs)$V(V NNI)
                wordv : V L NNI := empty()
                if wordProblem then
                    wordlist := append(wordlist, outword.i)
                    wordv := vector(wordlist)
                gporbi := orbv(i)
                for z0 in rejects while noresult repeat
                    z := copy(z0)
                    ppp := strip(z, i, false, orbv, sgsv, wordv)
                    noresult := testIdentity ppp.elt
                    if not(noresult) then
                        if wordProblem then
                            z := copy(z0)
                            ppp := strip(z, i, true, orbv, sgsv, wordv)
                        z := ppp.elt
                        word := ppp.lst
                for pt in gporbi.orb while noresult repeat
                    ppp   := cosetRep1(pt, wordProblem, gporbi, sgsv, wordv)
                    y1    := inv ppp.elt
                    word3 := ppp.lst
                    for jjj in 1..#sgs while noresult repeat
                        word         := []$(L NNI)
                        times!(z, qelt(sgsv, jjj), y1)
                        if wordProblem then word := qelt(wordv, jjj)
                        ppp := strip(z, i, false, orbv, sgsv, wordv)
                        z := ppp.elt
                        noresult := testIdentity z
                        if not(noresult) and wordProblem then
                            z := times (qelt(sgsv, jjj), y1)
                            ppp := strip(z, i, true, orbv, sgsv, wordv)
                            z := ppp.elt
                            word := append(ppp.lst, word)
                if not(noresult) then
                    for p in baseOfGroup for ii in 1.. repeat
                        basePoint    := 1
                        newBasePoint := true
                        if qelt(z, p) ~= p then
                            newBasePoint := false
                            basePoint    := (#baseOfGroup - ii + 1)::NNI
                            break
            noAnswer := not (testIdentity z)
            if noAnswer then
                add_cnt := add_cnt + 1
                -- we have missed something
                word2 := []$(L NNI)
                if wordProblem then
                    for wdi in word3 repeat
                        ttt := newGroup.wdi
                        while not (testIdentity ttt) repeat
                            word2 := cons(wdi, word2)
                            ttt   := times(ttt, newGroup.wdi)
                    word := append(word, word2)
                    word := shortenWord(word, group)
                if newBasePoint then
                    for i in 1..degree repeat
                        if z.i ~= i then
                            baseOfGroup := append(baseOfGroup, [ i ])
                            break
                    orbv := new(# baseOfGroup, dummy_rec)$(V REC)
                    out := cons(list  z, out)
                    if wordProblem then outword := cons(list word, outword)
                else
                    out.basePoint := cons(z, out.basePoint)
                    if wordProblem then
                        outword.basePoint := cons(word, outword.basePoint)
                kkk := basePoint
        sizeOfGroup : NNI := 1
        for j in 1..#baseOfGroup repeat
            sizeOfGroup := sizeOfGroup * # orbv(j).orb
        group.information := [sizeOfGroup, sgs, baseOfGroup, orbv, supp,
                              wordlist]$REC2
        sizeOfGroup
-}

||| With a small integer you get shorter words, but the
||| routine takes longer than the standard routine for longer words.
||| default value is:
||| initializeGroupForWordProblem gp 0 1
initializeGroupForWordProblem : (Eq set) => (gp : (List (Permutation set))) ->
                                (maxLoops:Nat) ->
                                (diff:Integer) -> (Rec2 set)
initializeGroupForWordProblem gp maxLoops diff =
  bsgs gp True maxLoops diff

--initializeGroupForWordProblem(gp) ==
--        initializeGroupForWordProblem(gp, 0, 1)

||| Constructor to initialise a permutation group.
||| Users are advised to use this contructor so that the strong
||| generators are initialsed properly.
||| @gp generators of the group
permutationGroup : (Eq set) => (gp : (List (Permutation set))) -> PermutationGroup set
permutationGroup gp =
  let
    information : Rec2 set = initializeGroupForWordProblem gp 0 1
  in
    PermGrp gp information

implementation Show set => Show (PermutationGroup set) where
    show a = "permutationGroup" ++(show (gens a)) ++
             "\n" ++ (show (information a))

------------------ Local Functions for examples below -----------

||| constructs the list of integers from 1 to n
li1n : Nat -> List Nat
li1n n =
  [1..n]

||| List List Cycle to List Permutation
llc2lp : (Eq set) => List (List (Cycle set)) -> List (Permutation set)
llc2lp llc = map cyclesToPermutation llc

lln2lc : (Eq set) => List (List set) -> List (Cycle set) 
lln2lc lln = map cycle.fromList lln

llln2llc : (Eq set) => List (List (List set)) -> List (List (Cycle set)) 
llln2llc llln = map lln2lc llln

llln2lp : (Eq set) => List (List (List set)) -> List (Permutation set)
llln2lp llln = llc2lp (llln2llc llln)

||| Converts an list of permutations each represented by a list
||| of cycles ( each of them represented as a list of Integers )
||| to the permutation group generated by these permutations.
llli2gp : (Eq set) => List (List (List set)) -> (PermutationGroup set)
llli2gp llln = permutationGroup (llln2lp llln)

||| n th entry in a list of integers
||| no type checking for now
nth' : (n : Nat) -> (l : List Nat) -> Nat
nth' Z (x::xs) = x
nth' (S n) (x::xs) = nth' n xs
nth' _     []      = 0

||| n th entry in a list of integers
||| no type checking for now
nth : (n : Int) -> (l : List Nat) -> Nat
nth n l =
  if n < 0
  then 0
  else nth' (the Nat (cast n)) l

------------------ Permutation Group Examples --------------------
---- Auxilary constructors to construct specific groups ----------

||| cyclicGroup([i1, ..., ik]) constructs the cyclic group of
||| order k acting on the integers i1, ..., ik.
||| Note: duplicates in the list will be removed.
cyclicGroup' : List Nat -> (PermutationGroup Nat)
cyclicGroup' l = llli2gp [[l]]

||| cyclicGroup(n) constructs the cyclic group of order n acting
||| on the integers 1, ..., n.
cyclicGroup : Nat -> (PermutationGroup Nat)
cyclicGroup n =
  cyclicGroup' (li1n n)

||| symmetricGroup' (li) constructs the symmetric group acting on
||| the integers in the list li, generators are the
||| cycle given by li and the 2-cycle (li.1, li.2).
||| Note: duplicates in the list will be removed.
symmetricGroup' : List Nat -> (PermutationGroup Nat)
symmetricGroup' l =
  --    l := removeDuplicates l
  --    length l = 0 => error "Cannot construct symmetric group on empty set !"
  case (length l) of
    (S Z) => llli2gp [[l]]
    (S (S Z)) => llli2gp [[l]]
    _ =>
      let
        tmp : List (List Nat) = [[nth' 0 l,nth' 1 l]]
        --length l < 3 => llli2gp [[l]]
        --llli2gp [[l], [[l.1, l.2]]]
      in
        llli2gp [ [ l ], tmp ]

||| symmetricGroup(n) constructs the symmetric group Sn
||| acting on the integers 1, ..., n, generators are the
||| n-cycle (1, ..., n) and the 2-cycle (1, 2).
symmetricGroup : Nat -> (PermutationGroup Nat)
symmetricGroup n = symmetricGroup' (li1n n)

||| dihedralGroup([i1, ..., ik]) constructs the dihedral group of
||| order 2k acting on the integers out of i1, ..., ik.
||| Note: duplicates in the list will be removed.
dihedralGroup' : List Nat -> (PermutationGroup Nat)
dihedralGroup' l =
  let
    -- l := removeDuplicates l
    -- length l < 3 => error "in dihedralGroup: Minimum of 3 elements needed !"
    -- tmp : List (List Nat) = [[l.i, l.(length l-i+1) ] for i in 1..(length l quo 2)]
    lenI :Int = (cast (length l))-1
    len :Nat = div (length l) 2
    tmp : List (List Nat) = [[nth' i l,nth (lenI - (cast i)) l] | i <- [0..len]]
  in
    llli2gp [ [ l ], tmp ]


||| dihedralGroup(n) constructs the dihedral group of order 2n
||| acting on integers 1, ..., N.
dihedralGroup : Nat -> (PermutationGroup Nat)
dihedralGroup n =
  case n of
    (S Z) => llli2gp [[[1]]] --n = 1 => symmetricGroup (2::PI)
    (S (S Z)) => llli2gp [[[1, 2]], [[3, 4]]]
    _ => dihedralGroup' (li1n n)

||| alternatingGroup(li) constructs the alternating group acting
||| on the integers in the list li, generators are in general the
||| n-2-cycle (li.3, ..., li.n) and the 3-cycle
||| (li.1, li.2, li.3), if n is odd and
||| product of the 2-cycle (li.1, li.2) with
||| n-2-cycle (li.3, ..., li.n) and the 3-cycle
||| (li.1, li.2, li.3), if n is even.
||| Note: duplicates in the list will be removed.
alternatingGroup' : List Nat -> (PermutationGroup Nat)
alternatingGroup' l =
  --    l := removeDuplicates l
  --    length l = 0 => error "Cannot construct symmetric group on empty set !"
  case (length l) of
    Z => llli2gp [[l]] -- error "Cannot construct alternating group on empty set"
    (S Z) => llli2gp [[[nth' 0 l]]] -- llli2gp [[[l.1]]]
    (S (S Z)) => llli2gp [[[nth' 0 l]]] -- llli2gp [[[l.1]]]
    (S (S (S Z))) => llli2gp [[[nth' 0 l,nth' 1 l,nth' 2 l]]] -- llli2gp [[[l.1, l.2, l.3]]]
    _ =>
      let
        tmp : List Nat = [nth' i l | i <- [3..(length l)]]
        gens : List (List (List Nat)) =
          if (modNatNZ (length l) 2 SIsNotZ) == 1 -- if odd 
          then [[tmp], [[nth' 0 l,nth' 1 l,nth' 2 l]]]
          else [[tmp ++ [nth' 0 l,nth' 1 l]], [[nth' 0 l,nth' 1 l,nth' 2 l]]]
      in  llli2gp gens

||| abelianGroup([n1, ..., nk]) constructs the abelian group that
||| is the direct product of cyclic groups with order ni.
abelianGroup : List Nat -> (PermutationGroup Nat)
abelianGroup l =
  let
    gens : List (List (List Nat)) =
      []
    --element : I := 1
    --    for n in l | n > 1 repeat
    --      gens := cons( list [i for i in element..(element+n-1) ], gens )
    --      element := element+n
  in llli2gp (if (length gens) == 0 then [[[1]]] else gens)


||| alternatingGroup(n) constructs the alternating group An
||| acting on the integers 1, ..., n,  generators are in general the
||| n-2-cycle (3, ..., n) and the 3-cycle (1, 2, 3)
||| if n is odd and the product of the 2-cycle (1, 2) with
||| n-2-cycle (3, ..., n) and the 3-cycle (1, 2, 3)
||| if n is even.
alternatingGroup : Nat -> (PermutationGroup Nat)
alternatingGroup n = alternatingGroup' (li1n n)

||| mathieu11(li) constructs the mathieu group acting on the 11
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| error, if li has less or more than 11 different entries.
mathieu11' : List Nat -> (PermutationGroup Nat)
mathieu11' l =
  -- permutations derived from the ATLAS
  --l := removeDuplicates l
  if length l == 11
  then
    let
      a : List (List Nat) = [[nth' 1 l, nth' 10 l], [nth' 2 l, nth' 8 l], [nth' 3 l, nth' 11 l], [nth' 5 l, nth' 7 l]]
    in 
      llli2gp [a, [[nth' 1 l, nth' 4 l, nth' 7 l, nth' 6 l], [nth' 2 l, nth' 11 l, nth' 10 l, nth' 9 l]]]
  else
    -- error "Exactly 11 integers for mathieu11 needed !"
    llli2gp [[[1]]]

||| mathieu11 constructs the mathieu group acting on the
||| integers 1, ..., 11.
mathieu11 : (PermutationGroup Nat)
mathieu11 = mathieu11' (li1n 11)

||| mathieu12(li) constructs the mathieu group acting on the 12
||| integers given in the list li.
||| Note: duplicates in the list will be removed
||| Error: if li has less or more than 12 different entries.
mathieu12' : List Nat -> (PermutationGroup Nat)
mathieu12' l =
  -- permutations derived from the ATLAS
  --l := removeDuplicates l
  if length l == 12
  then
    let
      a : List (List Nat) =
          [[nth' 1 l, nth' 2 l, nth' 3 l, nth' 4 l, nth' 5 l, nth' 6 l,
            nth' 7 l, nth' 8 l, nth' 9 l, nth' 10 l, nth' 11 l]]
    in llli2gp [a, [[nth' 1 l, nth' 6 l, nth' 5 l, nth' 8 l, nth' 3 l,
            nth' 7 l, nth' 4 l, nth' 2 l, nth' 9 l, nth' 10 l],
            [nth' 11 l, nth' 12 l]]]
  else
    -- error "Exactly 12 integers for mathieu12 needed !"
    llli2gp [[[1]]]

||| mathieu12 constructs the mathieu group acting on the
||| integers 1, ..., 12.
mathieu12 : (PermutationGroup Nat)
mathieu12 = mathieu12' (li1n 12)

||| mathieu22(li) constructs the mathieu group acting on the 22
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 22 different entries.
mathieu22' : List Nat -> (PermutationGroup Nat)
mathieu22' l =
  -- permutations derived from the ATLAS
  --l := removeDuplicates l
  if length l == 22
  then
    let
      a : List (List Nat) =
        [[nth' 1 l, nth' 2 l, nth' 4 l, nth' 8 l, nth' 16 l, nth' 9 l,
          nth' 18 l, nth' 13 l, nth' 3 l, nth' 6 l, nth' 12 l],
          [nth' 5 l, nth' 10 l, nth' 20 l, nth' 17 l, nth' 11 l,
          nth' 22 l, nth' 21 l, nth' 19 l, nth' 15 l, nth' 7 l, nth' 14 l]]
      b : List (List Nat) = [[nth' 1 l, nth' 2 l, nth' 6 l, nth' 18 l],
          [nth' 3 l, nth' 15 l], [nth' 5 l, nth' 8 l, nth' 21 l, nth' 13 l],
          [nth' 7 l, nth' 9 l, nth' 20 l, nth' 12 l], [nth' 10 l, nth' 16 l],
          [nth' 11 l, nth' 19 l, nth' 14 l, nth' 22 l]]
    in llli2gp [a, b]
  else
    -- error "Exactly 22 integers for mathieu22 needed !"
    llli2gp [[[1]]]

||| mathieu22 constructs the mathieu group acting on the
||| integers 1, ..., 22.
mathieu22 : (PermutationGroup Nat)
mathieu22 = mathieu22' (li1n 22)

||| mathieu23(li) constructs the mathieu group acting on the 23
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 23 different entries.
mathieu23' : List Nat -> (PermutationGroup Nat)
mathieu23' l =
  -- permutations derived from the ATLAS
  --l := removeDuplicates l
  if length l == 23
  then
    let
      a : List (List Nat) =
        [[nth' 1 l, nth' 2 l, nth' 3 l, nth' 4 l, nth' 5 l, nth' 6 l,
          nth' 7 l, nth' 8 l, nth' 9 l, nth' 10 l, nth' 11 l, nth' 12 l,
          nth' 13 l, nth' 14 l, nth' 15 l, nth' 16 l, nth' 17 l, nth' 18 l,
          nth' 19 l, nth' 20 l, nth' 21 l, nth' 22 l, nth' 23 l]]
      b : List (List Nat) =
        [[nth' 2 l, nth' 16 l, nth' 9 l, nth' 6 l, nth' 8 l],
         [nth' 3 l, nth' 12 l, nth' 13 l, nth' 18 l, nth' 4 l],
         [nth' 7 l, nth' 17 l, nth' 10 l, nth' 11 l, nth' 22 l],
         [nth' 14 l, nth' 19 l, nth' 21 l, nth' 20 l, nth' 15 l]]
    in llli2gp [a, b]
  else
    -- error "Exactly 23 integers for mathieu23 needed !"
    llli2gp [[[1]]]

||| mathieu23 constructs the mathieu group acting on the
||| integers 1, ..., 23.
mathieu23 : (PermutationGroup Nat)
mathieu23 = mathieu23' (li1n 23)

||| mathieu24(li) constructs the mathieu group acting on the 24
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 24 different entries.
mathieu24' : List Nat -> (PermutationGroup Nat)
mathieu24' l =
  -- permutations derived from the ATLAS
  --l := removeDuplicates l
  if length l == 24
  then
    let
      a : List (List Nat) =
        [[nth' 1 l, nth' 16 l, nth' 10 l, nth' 22 l, nth' 24 l],
        [nth' 2 l, nth' 12 l, nth' 18 l, nth' 21 l, nth' 7 l],
        [nth' 4 l, nth' 5 l, nth' 8 l, nth' 6 l, nth' 17 l],
        [nth' 9 l, nth' 11 l, nth' 13 l, nth' 19 l, nth' 15 l]]
      b : List (List Nat) =
        [[nth' 1 l, nth' 22 l, nth' 13 l, nth' 14 l, nth' 6 l,
        nth' 20 l, nth' 3 l, nth' 21 l, nth' 8 l, nth' 11 l],
        [nth' 2 l, nth' 10 l],
        [nth' 4 l, nth' 15 l, nth' 18 l, nth' 17 l, nth' 16 l,
        nth' 5 l, nth' 9 l, nth' 19 l, nth' 12 l, nth' 7 l],
        [nth' 23 l, nth' 24 l]]
    in llli2gp [a, b]
  else
    -- error "Exactly 24 integers for mathieu24 needed !"
    llli2gp [[[1]]]

||| mathieu24 constructs the mathieu group acting on the
||| integers 1, ..., 24.
mathieu24 : (PermutationGroup Nat)
mathieu24 = mathieu24' (li1n 24)

||| janko2(li) constructs the janko group acting on the 100
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 100 different entries
janko2' : List Nat -> (PermutationGroup Nat)
janko2' l =
  -- permutations derived from the ATLAS
  --l := removeDuplicates l
  if length l == 100
  then
    let
      a : List (List Nat) =
        [[nth' 2 l, nth' 3 l, nth' 4 l, nth' 5 l, nth' 6 l, nth' 7 l, nth' 8 l],
        [nth' 9 l, nth' 10 l, nth' 11 l, nth' 12 l, nth' 13 l, nth' 14 l, nth' 15 l],
        [nth' 16 l, nth' 17 l, nth' 18 l, nth' 19 l, nth' 20 l, nth' 21 l, nth' 22 l],
        [nth' 23 l, nth' 24 l, nth' 25 l, nth' 26 l, nth' 27 l, nth' 28 l, nth' 29 l],
        [nth' 30 l, nth' 31 l, nth' 32 l, nth' 33 l, nth' 34 l, nth' 35 l, nth' 36 l],
        [nth' 37 l, nth' 38 l, nth' 39 l, nth' 40 l, nth' 41 l, nth' 42 l, nth' 43 l],
        [nth' 44 l, nth' 45 l, nth' 46 l, nth' 47 l, nth' 48 l, nth' 49 l, nth' 50 l],
        [nth' 51 l, nth' 52 l, nth' 53 l, nth' 54 l, nth' 55 l, nth' 56 l, nth' 57 l],
        [nth' 58 l, nth' 59 l, nth' 60 l, nth' 61 l, nth' 62 l, nth' 63 l, nth' 64 l],
        [nth' 65 l, nth' 66 l, nth' 67 l, nth' 68 l, nth' 69 l, nth' 70 l, nth' 71 l],
        [nth' 72 l, nth' 73 l, nth' 74 l, nth' 75 l, nth' 76 l, nth' 77 l, nth' 78 l],
        [nth' 79 l, nth' 80 l, nth' 81 l, nth' 82 l, nth' 83 l, nth' 84 l, nth' 85 l],
        [nth' 86 l, nth' 87 l, nth' 88 l, nth' 89 l, nth' 90 l, nth' 91 l, nth' 92 l],
        [nth' 93 l, nth' 94 l, nth' 95 l, nth' 96 l, nth' 97 l, nth' 98 l, nth' 99 l] ]
      b : List (List Nat) =
        [[nth' 1 l, nth' 74 l, nth' 83 l, nth' 21 l, nth' 36 l, nth' 77 l, nth' 44 l,
        nth' 80 l, nth' 64 l, nth' 2 l, nth' 34 l, nth' 75 l, nth' 48 l, nth' 17 l, nth' 100 l],
        [nth' 3 l, nth' 15 l, nth' 31 l, nth' 52 l, nth' 19 l, nth' 11 l, nth' 73 l, nth' 79 l,
        nth' 26 l, nth' 56 l, nth' 41 l, nth' 99 l, nth' 39 l, nth' 84 l, nth' 90 l],
        [nth' 4 l, nth' 57 l, nth' 86 l, nth' 63 l, nth' 85 l, nth' 95 l, nth' 82 l,
        nth' 97 l, nth' 98 l, nth' 81 l, nth' 8 l, nth' 69 l, nth' 38 l, nth' 43 l, nth' 58 l],
        [nth' 5 l, nth' 66 l, nth' 49 l, nth' 59 l, nth' 61 l],
        [nth' 6 l, nth' 68 l, nth' 89 l, nth' 94 l, nth' 92 l, nth' 20 l, nth' 13 l,
        nth' 54 l, nth' 24 l, nth' 51 l, nth' 87 l, nth' 27 l, nth' 76 l, nth' 23 l, nth' 67 l],
        [nth' 7 l, nth' 72 l, nth' 22 l, nth' 35 l, nth' 30 l, nth' 70 l, nth' 47 l, nth' 62 l,
        nth' 45 l, nth' 46 l, nth' 40 l, nth' 28 l, nth' 65 l, nth' 93 l, nth' 42 l],
        [nth' 9 l, nth' 71 l, nth' 37 l, nth' 91 l, nth' 18 l, nth' 55 l, nth' 96 l,
        nth' 60 l, nth' 16 l, nth' 53 l, nth' 50 l, nth' 25 l, nth' 32 l, nth' 14 l, nth' 33 l],
        [nth' 10 l, nth' 78 l, nth' 88 l, nth' 29 l, nth' 12 l] ]
    in llli2gp [a, b]
  else
    -- error "Exactly 100 integers for janko2 needed !"
    llli2gp [[[1]]]


||| janko2 constructs the janko group acting on the
||| integers 1, ..., 100.
janko2 : (PermutationGroup Nat)
janko2 = janko2' (li1n 100)

||| rubiksGroup constructs the permutation group representing
||| Rubic's Cube acting on integers 10*i+j for
||| 1 <= i <= 6, 1 <= j <= 8.
||| The faces of Rubik's Cube are labelled in the obvious way
||| Front, Right, Up, Down, Left, Back and numbered from 1 to 6
||| in this given ordering, the pieces on each face
||| (except the unmoveable center piece) are clockwise numbered
||| from 1 to 8 starting with the piece in the upper left
||| corner. The moves of the cube are represented as permutations
||| on these pieces, represented as a two digit
||| integer ij where i is the numer of theface (1 to 6)
||| and j is the number of the piece on this face.
||| The remaining ambiguities are resolved by looking
||| at the 6 generators, which represent a 90 degree turns of the
||| faces, or from the following pictorial description.
||| Permutation group representing Rubic's Cube acting on integers
||| 10*i+j for 1 <= i <= 6, 1 <= j <=8.
|||
||| Rubik's Cube:   +-----+ +-- B   where: marks Side # :
|||                / U   /|/
|||               /     / |         F(ront)    <->    1
|||       L -->  +-----+ R|         R(ight)    <->    2
|||              |     |  +         U(p)       <->    3
|||              |  F  | /          D(own)     <->    4
|||              |     |/           L(eft)     <->    5
|||              +-----+            B(ack)     <->    6
|||                 ^
|||                 |
|||                 D
|||
||| The Cube's surface:
|||                                The pieces on each side
|||             +---+              (except the unmoveable center
|||             |567|              piece) are clockwise numbered
|||             |4U8|              from 1 to 8 starting with the
|||             |321|              piece in the upper left
|||         +---+---+---+          corner (see figure on the
|||         |781|123|345|          left).  The moves of the cube
|||         |6L2|8F4|2R6|          are represented as
|||         |543|765|187|          permutations on these pieces.
|||         +---+---+---+          Each of the pieces is
|||             |123|              represented as a two digit
|||             |8D4|              integer ij where i is the
|||             |765|              # of the side ( 1 to 6 for
|||             +---+              F to B (see table above ))
|||             |567|              and j is the # of the piece.
|||             |4B8|
|||             |321|
|||             +---+
|||
rubiksGroup : (PermutationGroup Nat)
rubiksGroup =
  let
    -- each generator represents a 90 degree turn of the appropriate
    -- side.
    f : List (List Nat) =
      [[11, 13, 15, 17], [12, 14, 16, 18], [51, 31, 21, 41], [53, 33, 23, 43], [52, 32, 22, 42]]
    r : List (List Nat) =
      [[21, 23, 25, 27], [22, 24, 26, 28], [13, 37, 67, 43], [15, 31, 61, 45], [14, 38, 68, 44]]
    u : List (List Nat) =
      [[31, 33, 35, 37], [32, 34, 36, 38], [13, 51, 63, 25], [11, 57, 61, 23], [12, 58, 62, 24]]
    d : List (List Nat) =
      [[41, 43, 45, 47], [42, 44, 46, 48], [17, 21, 67, 55], [15, 27, 65, 53], [16, 28, 66, 54]]
    l : List (List Nat) =
      [[51, 53, 55, 57], [52, 54, 56, 58], [11, 41, 65, 35], [17, 47, 63, 33], [18, 48, 64, 34]]
    b : List (List Nat) =
      [[61, 63, 65, 67], [62, 64, 66, 68], [45, 25, 35, 55], [47, 27, 37, 57], [46, 26, 36, 56]]
  in llli2gp [f, r, u, d, l, b]

||| youngGroup([n1, ..., nk]) constructs the direct product of the
||| symmetric groups Sn1, ..., Snk.
youngGroup' : List Nat -> (PermutationGroup Nat)
youngGroup' l =
  let
    gens : List (List (List Nat)) =
      []
    --element : I := 1
    --    for n in l | n > 1 repeat
    --      gens := cons(list [i for i in element..(element+n-1)], gens)
    --      if n >= 3 then gens := cons([[element, element+1]], gens)
    --      element := element+n
  in llli2gp (if (length gens) == 0 then [[[1]]] else gens)

--||| youngGroup(lambda) constructs the direct product of the symmetric
--||| groups given by the parts of the partition lambda.
--youngGroup : Partition -> (PermutationGroup Nat)
--      youngGroup(lambda : Partition) : PERMGRP I ==
--        youngGroup(convert(lambda)$Partition)

main : IO ()
main = 
  let
    c1 : PermutationGroup Nat = cyclicGroup 1
    c2 : PermutationGroup Nat = cyclicGroup 2
    c3 : PermutationGroup Nat = cyclicGroup 3
    c4 : PermutationGroup Nat = cyclicGroup 4
    s1 : PermutationGroup Nat = symmetricGroup 1
    s2 : PermutationGroup Nat = symmetricGroup 2
    s3 : PermutationGroup Nat = symmetricGroup 3
    s4 : PermutationGroup Nat = symmetricGroup 4
    d1 : PermutationGroup Nat = dihedralGroup 1
    d2 : PermutationGroup Nat = dihedralGroup 2
    d3 : PermutationGroup Nat = dihedralGroup 3
    d4 : PermutationGroup Nat = dihedralGroup 4
    a1 : PermutationGroup Nat = alternatingGroup 1
    a2 : PermutationGroup Nat = alternatingGroup 2
    a3 : PermutationGroup Nat = alternatingGroup 3
    a4 : PermutationGroup Nat = alternatingGroup 4
    a5 : PermutationGroup Nat = alternatingGroup 5
    
  in
    do
      putStrLn ("permutation group cyclic 1=" ++ (show c1))
      putStrLn ("permutation group cyclic 2=" ++ (show c2))
      putStrLn ("permutation group cyclic 3=" ++ (show c3))
      putStrLn ("permutation group cyclic 4=" ++ (show c4))
      putStrLn ("permutation group symmetric 1=" ++ (show s1))
      putStrLn ("permutation group symmetric 2=" ++ (show s2))
      putStrLn ("permutation group symmetric 3=" ++ (show s3))
      putStrLn ("permutation group symmetric 4=" ++ (show s4))
      putStrLn ("permutation group dihedral 1=" ++ (show d1))
      putStrLn ("permutation group dihedral 2=" ++ (show d2))
      putStrLn ("permutation group dihedral 3=" ++ (show d3))
      putStrLn ("permutation group dihedral 4=" ++ (show d4))
      putStrLn ("permutation group alternating 1=" ++ (show a1))
      putStrLn ("permutation group alternating 2=" ++ (show a2))
      putStrLn ("permutation group alternating 3=" ++ (show a3))
      putStrLn ("permutation group alternating 4=" ++ (show a4))
      putStrLn ("permutation group alternating 5=" ++ (show a5))
      
{-
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
-}
