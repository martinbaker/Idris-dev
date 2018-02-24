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
   ||| mp - moved points
   ||| Set of elements of S moved by some permutation.
   ||| That is, all points in generators, but don't
   ||| include if all generators map the points to themselves.
   ||| (needed for mapping between permutations on S and
   |||  internal representation)
   mp : FiniteSet set
   ||| wd - Gives representation of strong generators in terms
   ||| of original generators
   wd : List (List Nat)

implementation Show set => Show (Rec2 set) where
    show a = 
      "groupInfo order=" ++ (show (order a)) ++
      " sgset=" ++ (show (sgset a)) ++
      " gpbase=" ++ (show (gpbase a)) ++
      " orbs=" ++ (show (orbs a)) ++
      " mp=" ++ (show (mp a)) ++
      " wd=" ++ (show (wd a))

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
  in [FiniteSet.lookupIndexed 0 pre ima]

||| convert the definition of the group in terms of a mapping between
||| abitary sets to a definition using Nat which is easier to work with.
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
    q : List Nat = perm_to_vec Z (replicate degree 0) mp ggp degree
  in (newGroup,words,S ggg,ggps)

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
    then Record2 1 Nil Nil Nil mp Nil
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
        (newGroup,words,_,_) : (List (List Nat),List (List Nat),Nat,(List (Permutation set))) =
          -- params are: newGroup words mp degree ggg ggp
          convertToVect Nil Nil mp degree 0 group
      in
        Record2 degree sgset gpbase orbs mp wd

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

main : IO ()
main = 
  let
    p1:(Permutation Nat) = permSetFromList [1,2,3] [2,1,3]
    p2:(Permutation Nat) = permSetFromList [1,2,3] [1,3,2]
    group:List (Permutation Nat) = [p1,p2]
    pgroup:PermutationGroup Nat = permutationGroup group
  in
    putStrLn ("permutation group=" ++ (show pgroup))

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
