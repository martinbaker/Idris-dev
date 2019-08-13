module IDEModeCommands2

--import Core.Core
--import Core.Name
--import public Idris.REPLOpts

-------------------------------------------------------
-- All possible errors, carrying a location
public export
data Error 
    = Fatal Error -- flag as unrecoverable (so don't postpone awaiting further info)
{-    | CantConvert FC (Env Term vars) (Term vars) (Term vars)
    | CantSolveEq FC (Env Term vars) (Term vars) (Term vars)
    | PatternVariableUnifies FC (Env Term vars) Name (Term vars)
    | CyclicMeta FC Name
    | WhenUnifying FC (Env Term vars) (Term vars) (Term vars) Error
    | ValidCase FC (Env Term vars) (Either (Term vars) Error)
    | UndefinedName FC Name
    | InvisibleName FC Name (Maybe (List String))
    | BadTypeConType FC Name 
    | BadDataConType FC Name Name
    | NotCovering FC Name Covering
    | NotTotal FC Name PartialReason
    | LinearUsed FC Nat Name
    | LinearMisuse FC Name RigCount RigCount
    | BorrowPartial FC (Env Term vars) (Term vars) (Term vars)
    | BorrowPartialType FC (Env Term vars) (Term vars)
    | AmbiguousName FC (List Name)
    | AmbiguousElab FC (Env Term vars) (List (Term vars))
    | AmbiguousSearch FC (Env Term vars) (List (Term vars))
    | AllFailed (List (Maybe Name, Error))
    | RecordTypeNeeded FC (Env Term vars)
    | NotRecordField FC String (Maybe Name)
    | NotRecordType FC Name
    | IncompatibleFieldUpdate FC (List String)
    | InvalidImplicits FC (Env Term vars) (List (Maybe Name)) (Term vars)
    | TryWithImplicits FC (Env Term vars) (List (Name, Term vars))
    | BadUnboundImplicit FC (Env Term vars) Name (Term vars)
    | CantSolveGoal FC (Env Term vars) (Term vars)
    | DeterminingArg FC Name Int (Env Term vars) (Term vars)
    | UnsolvedHoles (List (FC, Name))
    | CantInferArgType FC (Env Term vars) Name Name (Term vars)
    | SolvedNamedHole FC (Env Term vars) Name (Term vars)
    | VisibilityError FC Visibility Name Visibility Name
    | NonLinearPattern FC Name
    | BadPattern FC Name
    | NoDeclaration FC Name
    | AlreadyDefined FC Name
    | NotFunctionType FC (Env Term vars) (Term vars)
    | RewriteNoChange FC (Env Term vars) (Term vars) (Term vars)
    | NotRewriteRule FC (Env Term vars) (Term vars)
    | CaseCompile FC Name CaseError 
    | MatchTooSpecific FC (Env Term vars) (Term vars)
    | BadDotPattern FC (Env Term vars) String (Term vars) (Term vars)
    | BadImplicit FC String
    | BadRunElab FC (Env Term vars) (Term vars)
    | GenericMsg FC String
    | TTCError TTCErrorMsg
    | FileErr String FileError
    | ParseFail FC ParseError
    | ModuleNotFound FC (List String)
    | CyclicImports (List (List String))
    | ForceNeeded
    | InternalError String

    | InType FC Name Error
    | InCon FC Name Error
    | InLHS FC Name Error
    | InRHS FC Name Error
-}

-- Core is a wrapper around IO that is specialised for efficiency.
export
record Core t where
  constructor MkCore
  runCore : IO (Either Error t)

-- from Idris2 TT.idr

public export
data Constant 
    = I Int
    | BI Integer
    | Str String
    | Ch Char
    | Db Double
    | WorldVal

    | IntType
    | IntegerType
    | StringType
    | CharType
    | DoubleType
    | WorldType

-- from Idris2 Core.Name
public export
data Name : Type where
     NS : List String -> Name -> Name -- in a namespace
     UN : String -> Name -- user defined name
     MN : String -> Int -> Name -- machine generated name
     PV : Name -> Int -> Name -- pattern variable name; int is the resolved function id
     DN : String -> Name -> Name -- a name and how to display it
     Nested : Int -> Name -> Name -- nested function name
     CaseBlock : Int -> Int -> Name -- case block nested in (resolved) name
     WithBlock : Int -> Int -> Name -- with block nested in (resolved) name
     Resolved : Int -> Name -- resolved, index into context

export Show Name where
  show (NS ns n) = "fix me" --showSep "." (reverse ns) ++ "." ++ show n
  show (UN x) = x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (DN str n) = str
  show (Nested outer inner) = show outer ++ ":" ++ show inner
  show (CaseBlock outer i) = "case block in " ++ show outer
  show (WithBlock outer i) = "with block in " ++ show outer
  show (Resolved x) = "$resolved" ++ show x

-------------------------------------------------------


%default covering

public export
data SExp = SExpList (List SExp)
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String

public export
data IDECommand
     = Interpret String
     | LoadFile String (Maybe Integer)
     | TypeOf String (Maybe (Integer, Integer))
     | CaseSplit Integer Integer String
     | AddClause Integer String
     | ExprSearch Integer String (List String) Bool
     | GenerateDef Integer String
     | MakeLemma Integer String
     | MakeCase Integer String
     | MakeWith Integer String
    
readHints : List SExp -> Maybe (List String)
readHints [] = Just []
readHints (StringAtom s :: rest)
    = do rest' <- readHints rest
         pure (s :: rest')
readHints _ = Nothing

export
getIDECommand : SExp -> Maybe IDECommand
getIDECommand (SExpList [SymbolAtom "interpret", StringAtom cmd])
    = Just $ Interpret cmd
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname])
    = Just $ LoadFile fname Nothing
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname, IntegerAtom l])
    = Just $ LoadFile fname (Just l)
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n])
    = Just $ TypeOf n Nothing
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n,
                         IntegerAtom l, IntegerAtom c])
    = Just $ TypeOf n (Just (l, c))
getIDECommand (SExpList [SymbolAtom "case-split", IntegerAtom l, IntegerAtom c, 
                         StringAtom n])
    = Just $ CaseSplit l c n
getIDECommand (SExpList [SymbolAtom "case-split", IntegerAtom l, StringAtom n])
    = Just $ CaseSplit l 0 n
getIDECommand (SExpList [SymbolAtom "add-clause", IntegerAtom l, StringAtom n])
    = Just $ AddClause l n
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n])
    = Just $ ExprSearch l n [] False
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, SExpList hs])
    = case readHints hs of
           Just hs' => Just $ ExprSearch l n hs' False
           _ => Nothing
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, SExpList hs, SymbolAtom mode])
    = case readHints hs of
           Just hs' => Just $ ExprSearch l n hs' (getMode mode)
           _ => Nothing
  where
    getMode : String -> Bool
    getMode m = m == "all"
getIDECommand (SExpList [SymbolAtom "generate-def", IntegerAtom l, StringAtom n])
    = Just $ GenerateDef l n
getIDECommand (SExpList [SymbolAtom "make-lemma", IntegerAtom l, StringAtom n])
    = Just $ MakeLemma l n
getIDECommand (SExpList [SymbolAtom "make-case", IntegerAtom l, StringAtom n])
    = Just $ MakeCase l n
getIDECommand (SExpList [SymbolAtom "make-with", IntegerAtom l, StringAtom n])
    = Just $ MakeWith l n
getIDECommand _ = Nothing

export
getMsg : SExp -> Maybe (IDECommand, Integer)
getMsg (SExpList [cmdexp, IntegerAtom num])
   = do cmd <- getIDECommand cmdexp
        pure (cmd, num)
getMsg _ = Nothing

escape : String -> String
escape = pack . concatMap escapeChar . unpack
  where
    escapeChar : Char -> List Char
    escapeChar '\\' = ['\\', '\\']
    escapeChar '"'  = ['\\', '\"']
    escapeChar c    = [c]

export
Show SExp where
  show (SExpList xs) = "fix me" --"(" ++ showSep " " (map show xs) ++ ")"
  show (StringAtom str) = "\"" ++ escape str ++ "\""
  show (BoolAtom b) = ":" ++ show b
  show (IntegerAtom i) = show i
  show (SymbolAtom s) = ":" ++ s

public export
interface SExpable a where
  toSExp : a -> SExp

export
SExpable SExp where
  toSExp = id

export
SExpable Bool where
  toSExp = BoolAtom

export
SExpable String where
  toSExp = StringAtom

export
SExpable Integer where
  toSExp = IntegerAtom

export
SExpable Int where
  toSExp = IntegerAtom . cast

export
SExpable Name where
  toSExp = SymbolAtom . show

export
(SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (x, y) 
      = case toSExp y of
             SExpList xs => SExpList (toSExp x :: xs)
             y' => SExpList [toSExp x, y']

export
SExpable a => SExpable (List a) where
  toSExp xs
      = SExpList (map toSExp xs)

export
sym : String -> Name
sym = UN

export
version : Int -> Int -> SExp
version maj min = toSExp (SymbolAtom "protocol-version", maj, min)

hex : File -> Int -> IO ()
hex (FHandle h) num = foreign FFI_C "fprintf" (Ptr -> String -> Int -> IO ()) h "%06x" num

sendLine : File -> String -> IO ()
sendLine (FHandle h) st = 
  map (const ()) (prim_fwrite h st)

{-export
send : SExpable a => File -> a -> Core ()
send f resp
    = do let r = show (toSExp resp) ++ "\n"
         coreLift $ hex f (cast (length r))
         coreLift $ sendLine f r
         coreLift $ fflush f
-}
