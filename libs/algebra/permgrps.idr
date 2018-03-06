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

{-
main : IO ()
main = 
  let
    p1:(Permutation Nat) = permSetFromList [1,2,3] [2,1,3]
    p2:(Permutation Nat) = permSetFromList [1,2,3] [1,3,2]
    group:List (Permutation Nat) = [p1,p2]
    pgroup:PermutationGroup Nat = permutationGroup group
    {- mp: FiniteSet String = fromList ["a","b","c"]
    a1: FiniteSet String = fromList ["a","b"]
    a2: FiniteSet String = fromList ["b","c"]
    b1: List Nat = finiteSetToIndex mp a1
    b2: List Nat = finiteSetToIndex mp a2
    cp1:(Permutation String) = permSetFromList ["a","b","c"] ["b","a","c"]
    cp2:(Permutation String) = permSetFromList ["a","b","c"] ["a","c","b"]
    c1: List Nat = permToVectSingle cp1 mp
    c2: List Nat = permToVectSingle cp2 mp
    d: List (List Nat) = permToVect1 [cp1,cp2] mp
    allMoved: FiniteSet String = fromList ["a","b","c"]
    preIm :(FiniteSet String) = preimage cp2
    preImIndex : List Nat = finiteSetToIndex allMoved preIm
    im:(FiniteSet String) = image cp2
    imIndex : List Nat = finiteSetToIndex allMoved im
    -}
    --a1:PermutationVec String = PermVec (fromList ["a","b","c"]) [1,0,2]
    --a2:PermutationVec String = PermVec (fromList ["a","b","c"]) [1,0,2]
    --a3:PermutationVec String = a1 * a2
    --b1:Nat = 0
    --b2:Nat = 1
    --b3:Nat = 2
    --b11:Nat = evalv a1 b1
    --b12:Nat = evalv a1 b2
    --b13:Nat = evalv a1 b3
    cyl : List (Cycle Nat) = [fromList [1,2],fromList [2,3,4]]
    prm : Permutation Nat = cyclesToPermutation cyl
    cy2 : List (Cycle Nat) = cyclesFromPermutation prm
    pv1: PermutationVec Nat = permToVect [p1]
    pv2: PermutationVec Nat = permToVect [p1,p2]
  in
    do
      putStrLn ("permutation group=" ++ (show pgroup))
      --putStrLn ("permVec a1:" ++ (show a1) ++
      --       " * a2:" ++ (show a2) ++
      --       " = a3:" ++ (show a3)
      --       )
      --putStrLn ("eval a1:" ++ (show a1) ++
      --       " = " ++ (show [b11,b12,b13])
      --       )
      {-putStrLn ("permToVect a1:" ++ (show a1) ++
             " -> b1:" ++ (show b1)
             )
      putStrLn ("permToVect a2:" ++ (show a2) ++
             " -> b2:" ++ (show b2)
             )
      putStrLn ("permToVectSingle cp1:" ++ (show cp1) ++ " mp:" ++ (show mp) ++
             " -> c1:" ++ (show c1)
             )
      putStrLn ("permToVectSingle cp2:" ++ (show cp2) ++ " mp:" ++ (show mp) ++
             " -> c2:" ++ (show c2)
             )
      putStrLn ("permToVect1 cp:[" ++ show cp1 ++ show cp2 ++ " mp:" ++ (show mp) ++
             "] -> d:" ++ (show d)
             )
      putStrLn ("preIm:" ++ (show preIm) ++
             " -> preImIndex:" ++ (show preImIndex) ++
             " -> im:" ++ (show im) ++
             " -> imIndex:" ++ (show imIndex)
             )
      -}
      putStrLn ("cycles:" ++ (show cyl))
      putStrLn ("perms:" ++ (show prm))
      putStrLn ("cycles2:" ++ (show cy2))
      putStrLn ("from:" ++ (show p1) ++
             " to:" ++ (show pv1)
             )
      putStrLn ("from:" ++ (show p2) ++
             " to:" ++ (show pv2)
             )
-}
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

{-
------------------ Local Functions for examples below -----------

||| Converts an list of permutations each represented by a list
||| of cycles ( each of them represented as a list of Integers )
||| to the permutation group generated by these permutations.
llli2gp : List (List (List (List Nat))) -> (Permutation Nat)
llli2gp l =
  (map(cycles, l))::PERMGRP I

------------------ Permutation Group Examples --------------------
---- Auxilary constructors to construct specific groups ----------

||| symmetricGroup' (li) constructs the symmetric group acting on
||| the integers in the list li, generators are the
||| cycle given by li and the 2-cycle (li.1, li.2).
||| Note: duplicates in the list will be removed.
symmetricGroup' : List Nat -> (Permutation Nat)
symmetricGroup' l =
    --    l := removeDuplicates l
    --    length l = 0 => error "Cannot construct symmetric group on empty set !"
        length l < 3 => llli2gp [[l]]
        llli2gp [[l], [[l.1, l.2]]]

||| symmetricGroup(n) constructs the symmetric group Sn
||| acting on the integers 1, ..., n, generators are the
||| n-cycle (1, ..., n) and the 2-cycle (1, 2).
symmetricGroup : Nat -> (Permutation Nat)
symmetricGroup n = symmetricGroup' (li1n n)

||| alternatingGroup(li) constructs the alternating group acting
||| on the integers in the list li, generators are in general the
||| n-2-cycle (li.3, ..., li.n) and the 3-cycle
||| (li.1, li.2, li.3), if n is odd and
||| product of the 2-cycle (li.1, li.2) with
||| n-2-cycle (li.3, ..., li.n) and the 3-cycle
||| (li.1, li.2, li.3), if n is even.
||| Note: duplicates in the list will be removed.
alternatingGroup' : List Nat -> (Permutation Nat)
        l := removeDuplicates l
        length l = 0 =>
          error "Cannot construct alternating group on empty set"
        length l < 3 => llli2gp [[[l.1]]]
        length l = 3 => llli2gp [[[l.1, l.2, l.3]]]
        tmp := [l.i for i in 3..(length l)]
        gens : L L L I := [[tmp], [[l.1, l.2, l.3]]]
        odd?(length l) => llli2gp gens
        gens.1 := cons([l.1, l.2], gens.1)
        llli2gp gens

||| alternatingGroup(n) constructs the alternating group An
||| acting on the integers 1, ..., n,  generators are in general the
||| n-2-cycle (3, ..., n) and the 3-cycle (1, 2, 3)
||| if n is odd and the product of the 2-cycle (1, 2) with
||| n-2-cycle (3, ..., n) and the 3-cycle (1, 2, 3)
||| if n is even.
alternatingGroup : Nat -> (Permutation Nat)
alternatingGroup n = alternatingGroup' (li1n n)

||| abelianGroup([n1, ..., nk]) constructs the abelian group that
||| is the direct product of cyclic groups with order ni.
abelianGroup' : List Nat -> (Permutation Nat)
abelianGroup l =
        gens := []$(L L L I)
        element : I := 1
        for n in l | n > 1 repeat
          gens := cons( list [i for i in element..(element+n-1) ], gens )
          element := element+n
        llli2gp
          #gens = 0 => [[[1]]]
          gens

||| cyclicGroup([i1, ..., ik]) constructs the cyclic group of
||| order k acting on the integers i1, ..., ik.
||| Note: duplicates in the list will be removed.
cyclicGroup' : List Nat -> (Permutation Nat)
      cyclicGroup(l : L I) : PERMGRP I ==
        l := removeDuplicates l
        length l = 0 => error "Cannot construct cyclic group on empty set"
        llli2gp [[l]]

||| cyclicGroup(n) constructs the cyclic group of order n acting
||| on the integers 1, ..., n.
cyclicGroup : Nat -> (Permutation Nat)
      cyclicGroup(n : PI) : PERMGRP I == cyclicGroup li1n n

||| dihedralGroup([i1, ..., ik]) constructs the dihedral group of
||| order 2k acting on the integers out of i1, ..., ik.
||| Note: duplicates in the list will be removed.
dihedralGroup' : List Nat -> (Permutation Nat)
      dihedralGroup(l : L I) : PERMGRP I ==
        l := removeDuplicates l
        length l < 3 => error "in dihedralGroup: Minimum of 3 elements needed !"
        tmp := [[l.i, l.(length l-i+1) ] for i in 1..(length l quo 2)]
        llli2gp [ [ l ], tmp ]


||| dihedralGroup(n) constructs the dihedral group of order 2n
||| acting on integers 1, ..., N.
dihedralGroup : Nat -> (Permutation Nat)
      dihedralGroup(n : PI) : PERMGRP I ==
        n = 1 => symmetricGroup (2::PI)
        n = 2 => llli2gp [[[1, 2]], [[3, 4]]]
        dihedralGroup li1n n


||| mathieu11(li) constructs the mathieu group acting on the 11
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| error, if li has less or more than 11 different entries.
mathieu11' : List Nat -> (Permutation Nat)
      mathieu11(l : L I) : PERMGRP I ==
      -- permutations derived from the ATLAS
        l := removeDuplicates l
        length l ~= 11 => error "Exactly 11 integers for mathieu11 needed !"
        a : L L I := [[l.1, l.10], [l.2, l.8], [l.3, l.11], [l.5, l.7]]
        llli2gp [a, [[l.1, l.4, l.7, l.6], [l.2, l.11, l.10, l.9]]]

||| mathieu11 constructs the mathieu group acting on the
||| integers 1, ..., 11.
mathieu11 : (Permutation Nat)
      mathieu11() : PERMGRP I == mathieu11 li1n 11

||| mathieu12(li) constructs the mathieu group acting on the 12
||| integers given in the list li.
||| Note: duplicates in the list will be removed
||| Error: if li has less or more than 12 different entries.
mathieu12' : List Nat -> (Permutation Nat)
      mathieu12(l : L I) : PERMGRP I ==
      -- permutations derived from the ATLAS
        l := removeDuplicates l
        length l ~= 12 => error "Exactly 12 integers for mathieu12 needed !"
        a : L L I :=
          [[l.1, l.2, l.3, l.4, l.5, l.6, l.7, l.8, l.9, l.10, l.11]]
        llli2gp [a, [[l.1, l.6, l.5, l.8, l.3, l.7, l.4, l.2, l.9, l.10], [l.11, l.12]]]

||| mathieu12 constructs the mathieu group acting on the
||| integers 1, ..., 12.
mathieu12 : (Permutation Nat)
      mathieu12() : PERMGRP I == mathieu12 li1n 12

||| mathieu22(li) constructs the mathieu group acting on the 22
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 22 different entries.
mathieu22' : List Nat -> (Permutation Nat)
      mathieu22(l : L I) : PERMGRP I ==
      -- permutations derived from the ATLAS
        l := removeDuplicates l
        length l ~= 22 => error "Exactly 22 integers for mathieu22 needed !"
        a : L L I := [[l.1, l.2, l.4, l.8, l.16, l.9, l.18, l.13, l.3, l.6, l.12],   _
          [l.5, l.10, l.20, l.17, l.11, l.22, l.21, l.19, l.15, l.7, l.14]]
        b : L L I := [[l.1, l.2, l.6, l.18], [l.3, l.15], [l.5, l.8, l.21, l.13],   _
          [l.7, l.9, l.20, l.12], [l.10, l.16], [l.11, l.19, l.14, l.22]]
        llli2gp [a, b]

||| mathieu22 constructs the mathieu group acting on the
||| integers 1, ..., 22.
mathieu22 : (Permutation Nat)
      mathieu22() : PERMGRP I == mathieu22 li1n 22

||| mathieu23(li) constructs the mathieu group acting on the 23
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 23 different entries.
mathieu23' : List Nat -> (Permutation Nat)
      mathieu23(l : L I) : PERMGRP I ==
      -- permutations derived from the ATLAS
        l := removeDuplicates l
        length l ~= 23 => error "Exactly 23 integers for mathieu23 needed !"
        a : L L I := [[l.1, l.2, l.3, l.4, l.5, l.6, l.7, l.8, l.9, l.10, l.11, l.12, l.13, l.14, _
                   l.15, l.16, l.17, l.18, l.19, l.20, l.21, l.22, l.23]]
        b : L L I := [[l.2, l.16, l.9, l.6, l.8], [l.3, l.12, l.13, l.18, l.4],              _
                   [l.7, l.17, l.10, l.11, l.22], [l.14, l.19, l.21, l.20, l.15]]
        llli2gp [a, b]

||| mathieu23 constructs the mathieu group acting on the
||| integers 1, ..., 23.
mathieu23 : (Permutation Nat)
      mathieu23() : PERMGRP I == mathieu23 li1n 23

||| mathieu24(li) constructs the mathieu group acting on the 24
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 24 different entries.
mathieu24' : List Nat -> (Permutation Nat)
      mathieu24(l : L I) : PERMGRP I ==
      -- permutations derived from the ATLAS
        l := removeDuplicates l
        length l ~= 24 => error "Exactly 24 integers for mathieu24 needed !"
        a : L L I := [[l.1, l.16, l.10, l.22, l.24], [l.2, l.12, l.18, l.21, l.7],          _
                   [l.4, l.5, l.8, l.6, l.17], [l.9, l.11, l.13, l.19, l.15]]
        b : L L I := [[l.1, l.22, l.13, l.14, l.6, l.20, l.3, l.21, l.8, l.11], [l.2, l.10],  _
                   [l.4, l.15, l.18, l.17, l.16, l.5, l.9, l.19, l.12, l.7], [l.23, l.24]]
        llli2gp [a, b]

||| mathieu24 constructs the mathieu group acting on the
||| integers 1, ..., 24.
mathieu24 : (Permutation Nat)
      mathieu24() : PERMGRP I == mathieu24 li1n 24

||| janko2(li) constructs the janko group acting on the 100
||| integers given in the list li.
||| Note: duplicates in the list will be removed.
||| Error: if li has less or more than 100 different entries
janko2' : List Nat -> (Permutation Nat)
      -- permutations derived from the ATLAS
        l := removeDuplicates l
        length l ~= 100 => error "Exactly 100 integers for janko2 needed !"
        a : L L I := [                                                            _
                 [l.2, l.3, l.4, l.5, l.6, l.7, l.8],                               _
                 [l.9, l.10, l.11, l.12, l.13, l.14, l.15],                         _
                 [l.16, l.17, l.18, l.19, l.20, l.21, l.22],                        _
                 [l.23, l.24, l.25, l.26, l.27, l.28, l.29],                        _
                 [l.30, l.31, l.32, l.33, l.34, l.35, l.36],                        _
                 [l.37, l.38, l.39, l.40, l.41, l.42, l.43],                        _
                 [l.44, l.45, l.46, l.47, l.48, l.49, l.50],                        _
                 [l.51, l.52, l.53, l.54, l.55, l.56, l.57],                        _
                 [l.58, l.59, l.60, l.61, l.62, l.63, l.64],                        _
                 [l.65, l.66, l.67, l.68, l.69, l.70, l.71],                        _
                 [l.72, l.73, l.74, l.75, l.76, l.77, l.78],                        _
                 [l.79, l.80, l.81, l.82, l.83, l.84, l.85],                        _
                 [l.86, l.87, l.88, l.89, l.90, l.91, l.92],                        _
                 [l.93, l.94, l.95, l.96, l.97, l.98, l.99] ]
        b : L L I := [
                [l.1, l.74, l.83, l.21, l.36, l.77, l.44, l.80, l.64, l.2, l.34, l.75, l.48, l.17, l.100], _
                [l.3, l.15, l.31, l.52, l.19, l.11, l.73, l.79, l.26, l.56, l.41, l.99, l.39, l.84, l.90], _
                [l.4, l.57, l.86, l.63, l.85, l.95, l.82, l.97, l.98, l.81, l.8, l.69, l.38, l.43, l.58], _
                [l.5, l.66, l.49, l.59, l.61], _
                [l.6, l.68, l.89, l.94, l.92, l.20, l.13, l.54, l.24, l.51, l.87, l.27, l.76, l.23, l.67], _
                [l.7, l.72, l.22, l.35, l.30, l.70, l.47, l.62, l.45, l.46, l.40, l.28, l.65, l.93, l.42], _
                [l.9, l.71, l.37, l.91, l.18, l.55, l.96, l.60, l.16, l.53, l.50, l.25, l.32, l.14, l.33], _
                [l.10, l.78, l.88, l.29, l.12] ]
        llli2gp [a, b]

||| janko2 constructs the janko group acting on the
||| integers 1, ..., 100.
janko2 : (Permutation Nat)
      janko2() : PERMGRP I == janko2 li1n 100

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
rubiksGroup : (Permutation Nat)
      rubiksGroup() : PERMGRP I ==
        -- each generator represents a 90 degree turn of the appropriate
        -- side.
        f : L L I :=
         [[11, 13, 15, 17], [12, 14, 16, 18], [51, 31, 21, 41], [53, 33, 23, 43], [52, 32, 22, 42]]
        r : L L I :=
         [[21, 23, 25, 27], [22, 24, 26, 28], [13, 37, 67, 43], [15, 31, 61, 45], [14, 38, 68, 44]]
        u : L L I :=
         [[31, 33, 35, 37], [32, 34, 36, 38], [13, 51, 63, 25], [11, 57, 61, 23], [12, 58, 62, 24]]
        d : L L I :=
         [[41, 43, 45, 47], [42, 44, 46, 48], [17, 21, 67, 55], [15, 27, 65, 53], [16, 28, 66, 54]]
        l : L L I :=
         [[51, 53, 55, 57], [52, 54, 56, 58], [11, 41, 65, 35], [17, 47, 63, 33], [18, 48, 64, 34]]
        b : L L I :=
         [[61, 63, 65, 67], [62, 64, 66, 68], [45, 25, 35, 55], [47, 27, 37, 57], [46, 26, 36, 56]]
        llli2gp [f, r, u, d, l, b]

||| youngGroup([n1, ..., nk]) constructs the direct product of the
||| symmetric groups Sn1, ..., Snk.
youngGroup' : List Nat -> (Permutation Nat)
      -- definition of the exported functions:
      youngGroup(l : L I) : PERMGRP I ==
        gens := []$(L L L I)
        element : I := 1
        for n in l | n > 1 repeat
          gens := cons(list [i for i in element..(element+n-1)], gens)
          if n >= 3 then gens := cons([[element, element+1]], gens)
          element := element+n
        llli2gp
          #gens = 0 => [[[1]]]
          gens

--||| youngGroup(lambda) constructs the direct product of the symmetric
--||| groups given by the parts of the partition lambda.
--youngGroup : Partition -> (Permutation Nat)
--      youngGroup(lambda : Partition) : PERMGRP I ==
--        youngGroup(convert(lambda)$Partition)

-}
