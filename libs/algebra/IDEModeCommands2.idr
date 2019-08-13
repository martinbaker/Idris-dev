module IDEModeCommands2

import Core2
--import Core.Name
--import public Idris.REPLOpts

import ParserLexer2
import Support2

-------------------------------------------------------

-- following from Core.FC

public export
FilePos : Type
FilePos = (Int, Int)

showPos : FilePos -> String
showPos (l, c) = show (l + 1) ++ ":" ++ show (c + 1)

public export
FileName : Type
FileName = String

public export
data FC = MkFC FileName FilePos FilePos
        | EmptyFC

-------------------------------------------------------
-- following from  Core.Env

-- Environment containing types and values of local variables
public export
data Env : (tm : List Name -> Type) -> List Name -> Type where
     Nil : Env tm []
     (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

-------------------------------------------------------
-- following from Core/TT.idr

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data LazyReason = LInf | LLazy | LUnknown

public export
data Term : List Name -> Type where
     Local : {name : _} ->
             FC -> Maybe Bool -> 
             (idx : Nat) -> .(IsVar name idx vars) -> Term vars
     Ref : FC -> NameType -> (name : Name) -> Term vars
     -- Metavariables and the scope they are applied to
     Meta : FC -> Name -> Int -> List (Term vars) -> Term vars
     Bind : FC -> (x : Name) -> 
            (b : Binder (Term vars)) -> 
            (scope : Term (x :: vars)) -> Term vars
     App : FC -> (fn : Term vars) -> (arg : Term vars) -> Term vars
     -- as patterns; since we check LHS patterns as terms before turning
     -- them into patterns, this helps us get it right. When normalising,
     -- we just reduce the inner term and ignore the 'as' part
     -- The 'as' part should really be a Name rather than a Term, but it's
     -- easier this way since it gives us the ability to work with unresolved
     -- names (Ref) and resolved names (Local) without having to define a
     -- special purpose thing. (But it'd be nice to tidy that up, nevertheless)
     As : FC -> (as : Term vars) -> (pat : Term vars) -> Term vars
     -- Typed laziness annotations
     TDelayed : FC -> LazyReason -> Term vars -> Term vars
     TDelay : FC -> LazyReason -> (ty : Term vars) -> (arg : Term vars) -> Term vars
     TForce : FC -> Term vars -> Term vars
     PrimVal : FC -> (c : Constant) -> Term vars
     Erased : FC -> Term vars
     TType : FC -> Term vars

public export
data Covering 
       = IsCovering
       | MissingCases (List (Term []))
       | NonCoveringCall (List Name)

public export
data PartialReason 
       = NotStrictlyPositive 
       | BadCall (List Name)
       | RecPath (List Name)

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n]) 
	   = "not terminating due to call to " ++ show n
  show (BadCall ns) 
	   = "not terminating due to calls to " ++ showSep ", " (map show ns) 
  show (RecPath ns) 
	   = "not terminating due to recursive path " ++ showSep " -> " (map show ns) 

public export
data RigCount = Rig0 | Rig1 | RigW

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

public export
data CaseError = DifferingArgNumbers
               | DifferingTypes
               | MatchErased (vars ** (Env Term vars, Term vars))
               | UnknownType

public export
data TTCErrorMsg
    = FormatOlder
    | FormatNewer
    | EndOfBuffer String
    | Corrupt String

export
Show TTCErrorMsg where
  show FormatOlder = "TTC data is in an older format"
  show FormatNewer = "TTC data is in a newer format"
  show (EndOfBuffer when) = "End of buffer when reading " ++ when
  show (Corrupt ty) = "Corrupt TTC data for " ++ ty

-------------------------------------------------------
-- All possible errors, carrying a location
public export
data Error 
    = Fatal Error -- flag as unrecoverable (so don't postpone awaiting further info)
    | CantConvert FC (Env Term vars) (Term vars) (Term vars)
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
