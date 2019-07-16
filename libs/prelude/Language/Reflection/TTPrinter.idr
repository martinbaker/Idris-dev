%language ElabReflection

implementation Show TTName where
  -- UN=A user-provided name
  show (UN s) = s
  -- NS=A name in some namespace
  show (NS t a) = (show t)++"."++(show a)
  -- MN=Machine-chosen names
  show (MN i s) = s++"_"++(show i)
  -- SN=Special name
  show (SN sn) = "TTName special name"

implementation Show TTUExp where
  -- Universe variable
  show (UVar s i) = "U=("++(show i)++":"++s++")"
  -- Explicit universe level
  show (UVal i) = "U="++(show i)

-- You must turn on the UniquenessTypes extension to use UniqueType or AnyType
--implementation Show Universe where
--  show NullType = "Universe:NullType"
--  show UniqueType = "Universe:UniqueType"
--  show AllTypes = "Universe:AllTypes"

implementation Show Const where
  show (I a) = show a
  show (BI a) = show a
  show (Fl a) = show a
  show (Ch a) = show a
  show (Str a) = show a
  show (B8 a) = show a
  show (B16 a) = show a
  show (B32 a) = show a
  show (B64 a) = show a
  show (AType a) = "AType"
  show StrType = "StrType"
  show VoidType = "VoidType"
  show Forgot = "Forgot"
  show WorldType = "WorldType"
  show TheWorld = "TheWorld"

implementation Show NameType where
  show Bound = "bound "
  show Ref = "de Bruijn "
  -- Data constructor with tag and number
  show (DCon i1 i2) = "{data constructor tag="++(show i1)++" number="++(show i2)++"}"
  -- Type constructor with tag and number
  show (TCon i1 i2) = "{type constructor tag="++(show i1)++" number="++(show i2)++"}"

mutual
 implementation Show TT where
  -- A reference to some name (P for Parameter) P NameType TTName TT
  show (P ty nm tt) = "{name ref " ++ (show ty)++
                      (show nm)++":"++ (show tt)++"<br/>}"
  -- Local variable uses de Bruijn index.
  show (V i) = "{TT:de Bruijn index="++ (show i)++"}"
  -- Bind a variable. ttn:TTName. b:Binder TT. tt:TT
  show (Bind ttn b tt) = (show ttn)++":(" ++
                         (show b)++"." ++ (show tt)++")<br/>}"
  show (App tt1 tt2) = "{TT:App<br/> tt1=" ++ (show tt1)++"<br/> tt2=" ++ (show tt2)++"<br/>}"
  show (TConst c) = "{TT:TConst c=" ++ (show c)++"}"
  show Erased = "{TT:Erased}"
  -- The type of types along (with universe constraints)
  show (TType ttuexp) = "Type<sub>"++ (show ttuexp)++"</sub>"
  show UType = "{TT:UType}"


 implementation Show (Binder TT) where
  show (Lam ty) = 
    let
      s : String = case ty of
        P typ nm tt => "{λ ("++(show nm)++":"++(show typ)++
                       ")."++(show tt)++"<br/>}"
        _ => "{Binder Lam:<br/> arg type="++(show ty)++"<br/>}"
    in
      s
  show (Pi ty kind) =
    let
      s : String = case ty of
        P typ nm tt => (show nm)++":"++(show typ)++
                       "."++(show tt)++"->"
        _ => "{Binder Pi:<br/> arg type="++(show ty)++"<br/> kind="++(show kind)++"<br/>}"
    in
      s
  show (Let ty val) = "{Binder Let:<br/> arg type="++(show ty)++"<br/> val="++(show val)++"<br/>}"
  show (Hole ty) = "{Binder Hole:<br/> arg type="++(show ty)++"<br/>}"
  show (GHole ty) = "{Binder GHole:<br/> arg type="++(show ty)++"<br/>}"

idNat : Nat -> Nat
idNat = %runElab (do
         intro `{{x}}
         fill (Var `{{x}})
         solve
         --debugMessage [TextPart ("getEnv=" ++show (!getEnv)++
         --                        "<br/><br/>getGoal="++show (!getGoal)++
         --                        "<br/><br/>getHoles="++show (!getHoles))] {a = ()}
         debugMessage [TextPart (show (!getGuess))] {a = ()}
         )

