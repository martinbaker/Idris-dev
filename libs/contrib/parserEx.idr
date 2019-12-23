module ParserExample

import Text/Lexer

{-

-}

%default total

public export
data Token = Number Integer
           | Operator String
           | Symbol String
           | OParen
           | CParen
           | EndInput

export
Show Token where
  show (Number x) = "number " ++ show x
  show (Operator x) = "operator " ++ x
  show (Symbol x) = x
  show OParen = "("
  show CParen = ")"
  show EndInput = "end of input"

{-
-- Special symbols - things which can't be a prefix of another symbol, and
-- don't match 'validSymbol'
export
operators : List String
operators 
    = ["+","-", "*", "/"]

export
opChars : String
opChars = "+-*/"

operator : Lexer
operator = some (oneOf opChars)


rawTokens : TokenMap Token
rawTokens =
    [(comment, Comment),
     (blockComment, Comment),
     (docComment, DocComment),
     (cgDirective, mkDirective),
     (holeIdent, \x => HoleIdent (assert_total (strTail x)))] ++
    map (\x => (exact x, Symbol)) symbols ++
    [(doubleLit, \x => DoubleLit (cast x)),
     (digits, \x => Literal (cast x)),
     (stringLit, \x => StrLit (stripQuotes x)),
     (charLit, \x => CharLit (stripQuotes x)),
     (ident, \x => if x `elem` keywords then Keyword x else Ident x),
     (space, Comment),
     (validSymbol, Symbol),
     (symbol, Unrecognised)]
-}
