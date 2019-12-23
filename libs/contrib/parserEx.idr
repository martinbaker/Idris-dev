module ParserExample

import Text.Lexer

{-
to run:

cd Idris-dev/libs/contrib
idris -p contrib parserEx.idr
     ____    __     _
    /  _/___/ /____(_)____
    / // __  / ___/ / ___/     Version 1.3.2
  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/
 /___/\__,_/_/  /_/____/       Type :? for help

Idris is free software with ABSOLUTELY NO WARRANTY.
For details type :warranty.
Type checking ./Text/Token.idr
Type checking ./Text/Quantity.idr
Type checking ./Control/Delayed.idr
Type checking ./Data/Bool/Extra.idr
Type checking ./Text/Lexer/Core.idr
Type checking ./Text/Lexer.idr
Type checking ./parserEx.idr
*parserEx> 

-}

%default total

public export
data Token = Number String --Integer
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

-- arithmetic operators plus, minus, multiply and divide.
export
opChars : String
opChars = "+-*/"

operator : Lexer
operator = some (oneOf opChars)

rawTokens : TokenMap Token
rawTokens =
    [(digits, \x => Number x),
     (operator, \x => Operator x),
     (symbol, \x => Symbol x),
     (is '(' ,\x => OParen),
     (is ')' ,\x => CParen)]

