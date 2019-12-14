module IDEModeParser2

--import IDEModeCommands2

import Core2 -- to show Recognise
import Parser2
import ParserLexer2
import Support2
import Lexer2
import public Control.Delayed

-- Slightly different lexer than the source language because we are more free
-- as to what can be identifiers, and fewer tokens are supported. But otherwise,
-- we can reuse the standard stuff

--%hide ParserLexer2.symbols

--symbols : List String
--symbols = ["(", ":", ")"]

{-
-- An identifier starts with alpha character followed by alpha-numeric
ident : Lexer
ident = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent '-' = True
    validIdent '\'' = True
    validIdent x = isAlphaNum x

ideTokens : TokenMap Token
ideTokens = 
    map (\x => (exact x, Symbol)) symbols ++
    [(digits, \x => Literal (cast x)),
     (stringLit, \x => StrLit (stripQuotes x)),
     (ident, Ident),
     (space, Comment)]
  where
    stripQuotes : String -> String
    -- ASSUMPTION! Only total because we know we're getting quoted strings.
    stripQuotes = assert_total (strTail . reverse . strTail . reverse)

idelex : String -> Either (Int, Int, String) (List (TokenData Token))
idelex str
    = case lex ideTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++ 
                                      [MkToken l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True
-}

{- remove parser for now
sexp : Rule SExp
sexp
    = do symbol ":"; exactIdent "True"
         pure (BoolAtom True)
  <|> do symbol ":"; exactIdent "False"
         pure (BoolAtom False)
  <|> do i <- intLit
         pure (IntegerAtom i)
  <|> do str <- strLit
         pure (StringAtom str)
  <|> do symbol ":"; x <- unqualifiedName 
         pure (SymbolAtom x)
  <|> do symbol "("
         xs <- many sexp
         symbol ")"
         pure (SExpList xs)

ideParser : String -> Grammar (TokenData Token) e ty -> Either ParseError ty
ideParser str p 
    = case lex str of -- was idelex
           Left err => Left $ LexFail err
           Right toks => 
              case parse p toks of
                   Left (Error err []) => 
                          Left $ ParseFail err Nothing []
                   Left (Error err (t :: ts)) => 
                          Left $ ParseFail err (Just (line t, col t))
                                               (map tok (t :: ts))
                   Right (val, _) => Right val

export
parseSExp : String -> Either ParseError SExp
parseSExp inp
    = ideParser inp (do c <- sexp; eoi; pure c)
-}
{-
Show Token where
  show (Ident x) = "identifier " ++ x
  show (HoleIdent x) = "hole identifier " ++ x
  show (Literal x) = "literal " ++ show x
  show (StrLit x) = "string " ++ show x
  show (CharLit x) = "character " ++ show x
  show (DoubleLit x) = "double " ++ show x
  show (Symbol x) = "symbol " ++ x
  show (Keyword x) = x
  show (Unrecognised x) = "Unrecognised " ++ x
  show (Comment x) = "comment"
  show (DocComment x) = "doc comment"
  show (CGDirective x) = "CGDirective " ++ x
  show EndInput = "end of input"
-}

{-
Core2 uses import public Control.Delayed
which uses Inf
-}

--show3 : (Lazy (TokenData Token)) -> String
--show3 t = show (line (Force t)) -- ********* error show gives messy result **********

Show x => Show (Inf x) where
  show y = show (Force y)
  --show y = "a"

Show x => Show (Lazy x) where
  show y = show (Force y)
  --show y = "b"

--Show x => Show (Delayed x) where
--  show y = show (Force y)

-- tokenData is defined like this:
--record TokenData a where
--  constructor MkToken
--  line : Int
--  col : Int
--  tok : a
show3 : (TokenData Token) -> String
--show3 t = show (line t) ++ ":" ++ show (col t) ++":" ++ show (tok t)
show3 t = show (line t) -- ********* error show gives messy result **********
--show3 t = show (3) -- works as expected
--show3 t = show (Delay 3) -- Can't find implementation for Show (Delayed t Integer)


show2 : (List (TokenData Token)) -> String
show2 xs = "[" ++ show' "" xs ++ "]" where
        show' acc []        = acc
        show' acc [x]       = acc ++ show3 x
        --show' acc [x]       = acc ++ "3"
        show' acc (x :: xs) = show' (acc ++ show3 x ++ ", ") xs

-----------------------------------------------------
-- the following is a specific show for looking
-- at TokenMap for example:
-- showTM rawTokens
-----------------------------------------------------
showTM5 : (Recognise c) -> String
--showTM5 Empty = "Empty"
--showTM5 Fail = "Fail"
--showTM5 (Lookahead p x) = "Lookahead"
--showTM5 (Pred x) = "Pred"
--showTM5 (SeqEat x y) = "SeqEat"
--showTM5 (SeqEmpty x y) = "SeqEmpty"
--showTM5 (Alt x y) = "Alt"
showTM5 _ = "_"

showTM4 : (Recognise c) -> String
showTM4 Empty = "Empty"
showTM4 Fail = "Fail"
showTM4 (Lookahead p x) = "Lookahead"
showTM4 (Pred x) = "Pred"
showTM4 (SeqEat x y) = "SeqEat" ++ (showTM5 x) ++ "," ++ (showTM5 y)
showTM4 (SeqEmpty x y) = "SeqEmpty " ++ (showTM5 x) ++ "||" ++ (showTM5 y)
showTM4 (Alt x y) = "Alt" ++ (showTM5 x) ++ "&&" ++ (showTM5 y)
showTM4 _ = "_"

showTM3 : (Lexer, String -> tokenType) -> String
showTM3 (x, y) = "(" ++ showTM4 x ++ ", " ++ "s->t" ++ ")"

showTM2 : (List (Lexer, String -> tokenType)) -> String
showTM2 xs = "[" ++ show' "" xs ++ "]" where
        show' : String -> (List (Lexer, String -> tokenType)) -> String
        show' acc []        = acc
        show' acc [x]       = acc ++ showTM3 x
        show' acc (x :: xs) = show' (acc ++ showTM3 x ++ ", ") xs

showTM : (TokenMap Token) -> String
showTM tm = showTM2 tm

---------------------------------------------------------
-- An alternative way to show Recognise data.
-- First convert to an eager version of Recognise
-- then show.
-- To use: showE rawTokens
---------------------------------------------------------

||| An eager version of Recognise from Core.
public export
data ERecognise : Type where
     EEmpty : ERecognise
     EFail : ERecognise
     ELookahead : (positive : Bool) -> ERecognise -> ERecognise
     EPred : (Char -> Bool) -> ERecognise
     ESeqEat : ERecognise -> ERecognise -> ERecognise
     ESeqEmpty : ERecognise -> ERecognise -> ERecognise
     EAlt : ERecognise -> ERecognise -> ERecognise
     ENull : ERecognise

--export
--Show ERecognise where
--  show EEmpty = "Empty"
--  show EFail = "Fail"
--  show (ELookahead p x) = "Lookahead" ++ (show p) ++ "," ++ (show x)
--  show (EPred p) = "Pred"
--  show (ESeqEat x y) = "SeqEat" ++ (show x) ++ "," ++ (show y)
--  show (ESeqEmpty x y) = "SeqEmpty" ++ (show x) ++ "," ++ (show y)
--  show (EAlt x y) = "Alt" ++ (show x) ++ "," ++ (show y)
--  show ENull = "..."

showE4 : ERecognise -> String
showE4 EEmpty = "Empty"
showE4 EFail = "Fail"
showE4 (ELookahead p x) = "Lookahead" ++ (show p) ++ "," ++ (showE4 x)
showE4 (EPred p) = "Pred"
showE4 (ESeqEat x y) = "SeqEat" ++ (showE4 x) ++ "," ++ (showE4 y)
showE4 (ESeqEmpty x y) = "SeqEmpty" ++ (showE4 x) ++ "," ++ (showE4 y)
showE4 (EAlt x y) = "Alt" ++ (showE4 x) ++ "," ++ (showE4 y)
showE4 ENull = "..."

toEagerRecognise : Nat -> Recognise c -> ERecognise
toEagerRecognise _ Empty = EEmpty
toEagerRecognise _ Fail = EFail
toEagerRecognise Z (Lookahead p x) = ELookahead p ENull
toEagerRecognise _ (Pred p) = EPred p
toEagerRecognise Z (SeqEat x y) = ESeqEat ENull ENull
toEagerRecognise Z (SeqEmpty x y) = ESeqEmpty ENull ENull
toEagerRecognise Z (Alt x y) = EAlt ENull ENull
toEagerRecognise (S n) (Lookahead p x) = ELookahead p (toEagerRecognise n x)
toEagerRecognise (S n) (SeqEat x y) = ESeqEat (toEagerRecognise n x) (toEagerRecognise n y)
toEagerRecognise (S n) (SeqEmpty x y) = ESeqEmpty (toEagerRecognise n x) (toEagerRecognise n y)
toEagerRecognise (S n) (Alt x y) = EAlt (toEagerRecognise n x) (toEagerRecognise n y)
toEagerRecognise _ _ = ENull

showE3 : (Lexer, String -> tokenType) -> String
showE3 (x, y) = "(" ++ showE4 (toEagerRecognise 1 x) ++ ", " ++ "s->t" ++ ")"

showE2 : (List (Lexer, String -> tokenType)) -> String
showE2 xs = "[" ++ show' "" xs ++ "]" where
        show' : String -> (List (Lexer, String -> tokenType)) -> String
        show' acc []        = acc
        show' acc [x]       = acc ++ showE3 x
        show' acc (x :: xs) = show' (acc ++ showE3 x ++ ", ") xs

showE : (TokenMap Token) -> String
showE tm = showE2 tm

---------------------------------------------------------------------
-- display some recognisers
showR : (Recognise c) -> String
showR Empty = "Empty"
showR Fail = "Fail"
showR (Lookahead p x) = "Lookahead"
showR (Pred x) = "Pred"
showR (SeqEat x y) = "SeqEat" ++ (showR x) ++ "," ++ (showR y)
showR (SeqEmpty x y) = "SeqEmpty " ++ (showR x) ++ "||" ++ (showR y)
showR (Alt x y) = "Alt" ++ (showR x) ++ "&&" ++ (showR y)
showR _ = "_"

showLex : String
showLex = showE4 (toEagerRecognise 2 (exact "ab"))

showLex2 : String
showLex2 = showE4 (toEagerRecognise 2 (like 'a'))

--------------------------------------------------------------------
myCountNLs : List Char -> Nat
myCountNLs str = List.length (filter (== '\n') str)

myGetCols : String -> Int -> Int
myGetCols x c
         = case span (/= '\n') (reverse x) of
                (incol, "") => c + cast (length incol)
                (incol, _) => cast (length incol)


myGetFirstToken : TokenMap a -> StrLen -> (line : Int) -> (col : Int) -> Maybe (TokenData a, Int, Int, StrLen)
myGetFirstToken [] str line col = Nothing
myGetFirstToken ((lex, fn) :: ts) str line col
        = case takeToken lex str of
               Just (tok, rest) => Just (MkToken line col (fn tok),
                                         line + cast (myCountNLs (unpack tok)),
                                         myGetCols tok col, rest)
               Nothing => myGetFirstToken ts str line col

-- gives:
--*IDEModeParser2> myGetFirstToken rawTokens (mkStr "23 test") 0 0
--Just (MkToken 0 0 (Literal 23),
--      0,
--      case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "32" of
--        (incol, "") => c + cast (length incol)
--        (incol, b) => cast (length incol),
--      MkStrLen " test" 5) : Maybe (TokenData Token, Int, Int, StrLen)
--*IDEModeParser2> 

myTakeToken : TokenMap a -> Maybe Lexer
myTakeToken [] = Nothing
myTakeToken ((lex, fn) :: ts) = Just lex

-- gives:
--*IDEModeParser2> myTakeToken rawTokens
--Just (SeqEat (SeqEat (Pred (\ARG => intToBool (prim__eqChar ARG '-')))
--                     (Delay (is '-')))
--             (Delay (many (Pred (\ARG =>
--                                   not (intToBool (prim__eqChar ARG
--                                                                '\n'))))))) : Maybe (Recognise True)
--*IDEModeParser2> 

-- TokenMap has this type:
-- TokenMap tokenType = List (Lexer, String -> tokenType)
showFirstLex : TokenMap Token -> String -> (String,Token)
showFirstLex [] str = ("token map empty",EndInput)
showFirstLex ((lex, fn) :: ts) str
        = case takeToken lex (mkStr str) of
               Just (tok, rest) => (tok,(fn tok))
               Nothing => showFirstLex ts str

--------------------------------------------------------------------

||| show list of tokens for given string
||| Used for debuging
export
lexAlgebra : String -> String
lexAlgebra str
    = case lex str of
           Left err => "lex error " ++ (show err)
           --Right toks => show2 toks
           Right toks => show toks

--------------------------------------------------------------------

myTokenMap : TokenMap Token
myTokenMap = [(is 'a',CharLit)]

myTokenPred : Token -> Maybe String
myTokenPred t = Just "a"
