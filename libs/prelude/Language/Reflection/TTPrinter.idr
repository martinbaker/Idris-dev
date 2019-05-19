%language ElabReflection

implementation Show TTName where
  show (UN s) = "`{{"++s++"}}"
  show (NS t a) = "{"++(show t)++"."++(show a)++"}"
  show (MN i s) = "{"++s++"_"++(show i)++"}"
  show (SN sn) = "TTName special name"

implementation Show TTUExp where
  show (UVar s i) = "ext="++s++"#"++(show i)
  show (UVal i) = "U"++(show i)

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
  show Bound = "NameType just bound by intro"
  show Ref = "NameType de Bruijn indexed"
  show (DCon i1 i2) = "{NameType data constructor i1="++(show i1)++" i2"++(show i2)++"}"
  show (TCon i1 i2) = "{type const tag="++(show i1)++","++(show i2)++"}"

mutual
 implementation Show TT where
  show (P ty nm tt) = "{TT:Parameter name ref<br/> NameType=" ++ (show ty)++
                      "<br/> TTName="++ (show nm)++"<br/> TT="++ (show tt)++"<br/>}"
  show (V i) = "{TT:de Bruijn index="++ (show i)++"}"
  show (Bind ttn b tt) = "{TT:Bind<br/> name=" ++ (show ttn)++"<br/> binder=" ++
                         (show b)++"<br/> tt=" ++ (show tt)++"<br/>}"
  show (App tt1 tt2) = "{TT:App<br/> tt1=" ++ (show tt1)++"<br/> tt2=" ++ (show tt2)++"<br/>}"
  show (TConst c) = "{TT:TConst c=" ++ (show c)++"}"
  show Erased = "{TT:Erased}"
  show (TType t) = "{TT:TType<br/> tt="++ (show t)++"<br/>}"
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
        P typ nm tt => "{Π ("++(show nm)++":"++(show typ)++
                       ")."++(show tt)++"<br/>}"
        _ => "{Binder Pi:<br/> arg type="++(show ty)++"<br/> kind="++(show kind)++"<br/>}"
    in
      s
  show (Let ty val) = "{Binder Let:<br/> arg type="++(show ty)++"<br/> val="++(show val)++"<br/>}"
  show (Hole ty) = "{Binder Hole:<br/> arg type="++(show ty)++"<br/>}"
  show (GHole ty) = "{Binder GHole:<br/> arg type="++(show ty)++"<br/>}"

idNat : Nat -> Nat
idNat = %runElab (do
         debugMessage [TextPart ("getEnv=" ++show (!getEnv)++
                                 "<br/><br/>getGoal="++show (!getGoal)++
                                 "<br/><br/>getHoles="++show (!getHoles))] {a = ()}
         intro `{{x}}
         fill (Var `{{x}})
         --debugMessage [TextPart (show (!getGuess))]
         solve
         debugMessage [TextPart ("getEnv=" ++show (!getEnv)++
                                 "<br/><br/>getGoal="++show (!getGoal)++
                                 "<br/><br/>getHoles="++show (!getHoles))]
         )

