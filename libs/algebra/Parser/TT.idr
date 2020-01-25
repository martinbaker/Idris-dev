module Parser.TT

--************** from  Idris2/src/Core/Name.idr 
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

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

||| Check whether a given character is a valid identifier character
export
identChar : Char -> Bool
identChar x = isAlphaNum x || x == '_' || x == '\''

export Show Name where
  show (NS ns n) = showSep "." (reverse ns) ++ "." ++ show n
  show (UN x) = x
  show (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
  show (PV n d) = "{P:" ++ show n ++ ":" ++ show d ++ "}"
  show (DN str n) = str
  show (Nested outer inner) = show outer ++ ":" ++ show inner
  show (CaseBlock outer i) = "case block in " ++ show outer
  show (WithBlock outer i) = "with block in " ++ show outer
  show (Resolved x) = "$resolved" ++ show x

export
Eq Name where
    (==) (NS ns n) (NS ns' n') = n == n' && ns == ns'
    (==) (UN x) (UN y) = x == y
    (==) (MN x y) (MN x' y') = y == y' && x == x'
    (==) (PV x y) (PV x' y') = x == x' && y == y'
    (==) (DN _ n) (DN _ n') = n == n'
    (==) (Nested x y) (Nested x' y') = x == x' && y == y'
    (==) (CaseBlock x y) (CaseBlock x' y') = y == y' && x == x'
    (==) (WithBlock x y) (WithBlock x' y') = y == y' && x == x'
    (==) (Resolved x) (Resolved x') = x == x'
    (==) _ _ = False

--************** end of from  Idris2/src/Core/Name.idr 

public export
data Visibility = Private | Export | Public

public export
data FnOpt : Type where
       Inline : FnOpt
       -- Flag means the hint is a direct hint, not a function which might
       -- find the result (e.g. chasing parent interface dictionaries)
       Hint : Bool -> FnOpt
       -- Flag means to use as a default if all else fails
       GlobalHint : Bool -> FnOpt
       ExternFn : FnOpt
       -- Defined externally, list calling conventions
       ForeignFn : List String -> FnOpt
       -- assume safe to cancel arguments in unification
       Invertible : FnOpt
       Total : FnOpt
       Covering : FnOpt
       PartialOK : FnOpt
       Macro : FnOpt

public export
data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors
       UniqueSearch : DataOpt

public export
data LazyReason = LInf | LLazy | LUnknown
