--********** the following is from Idris2/src/Core/FC.idr
public export
FilePos : Type
FilePos = (Int, Int)

showPos : FilePos -> String
showPos (l, c) = show (l + 1) ++ ":" ++ show (c + 1)

public export
FileName : Type
FileName = String

||| A file context is a filename together with starting and ending positions
public export
data FC = MkFC FileName FilePos FilePos
        | EmptyFC
--********** end of insert from Idris2/src/Core/FC.idr
