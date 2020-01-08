module ParserExample

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

{-
Idris REPL does not input and display mathematical structures, such as
complex numbers or matricies, in mathematical notation. This code aims
to implement a REPL designed for mathematical structures.

to run:
cd Idris-dev/libs/contrib
idris -p contrib algebraREPL.idr
-}

%default total

public export
data ExpressionToken = Number Integer
           | Operator String
           | OParen
           | CParen
           | Comment String
           | EndInput

export
Show ExpressionToken where
  show (Number x) = "number " ++ show x
  show (Operator x) = "operator " ++ x
  show OParen = "("
  show CParen = ")"
  show (Comment _) = "comment"
  show EndInput = "end of input"

export
Show (TokenData ExpressionToken) where
  show (MkToken l c t) = "line=" ++ show l ++ " col=" ++ show c ++ "tok=" ++ show t

-- integer arithmetic operators plus, minus and multiply.
export
opChars : String
opChars = "+-*"

operator : Lexer
operator = some (oneOf opChars)

toInt' : String -> Integer
toInt' = cast

-- from https://github.com/edwinb/Idris2/blob/master/src/Parser/Lexer.idr
comment : Lexer
comment = is '-' <+> is '-' <+> many (isNot '\n')

expressionTokens : TokenMap ExpressionToken
expressionTokens =
    [(digits, \x => Number (toInt' x)),
     (operator, \x => Operator x),
     (is '(' ,\x => OParen),
     (is ')' ,\x => CParen),
     (space, Comment),
     (comment, Comment)]

-- parser

-- from  Idris2/src/Parser/Support.idr 
public export
Rule : Type -> Type
Rule ty = Grammar (TokenData ExpressionToken) True ty

export
intLiteral : Rule Integer
intLiteral
    = terminal --"Expected integer literal"
               (\x => case tok x of
                           Number i => Just i
                           _ => Nothing)

openParen : Rule Integer
openParen = terminal (\x => case tok x of
                           OParen => Just 0
                           _ => Nothing)

closeParen : Rule Integer
closeParen = terminal (\x => case tok x of
                           CParen => Just 0
                           _ => Nothing)

commentSpace : Rule Integer
commentSpace = terminal (\x => case tok x of
                           Comment s => Just 0
                           _ => Nothing)

||| Matches if this is an operator token and string matches, that is,
||| it is the required type of operator.
op : String -> Rule Integer
op s = terminal (\x => case tok x of
                           (Operator s1) => if s==s1 then Just 0 else Nothing
                           _ => Nothing)

paren : Rule Integer -> Rule Integer
paren exp = ((openParen <* commentSpace) <|> openParen)
             *> exp <*
             ((closeParen <* commentSpace) <|> closeParen)

addInt : Integer -> Integer -> Integer
addInt a b = a+b

subInt : Integer -> Integer -> Integer
subInt a b = a-b

multInt : Integer -> Integer -> Integer
multInt a b = a*b

partial
expr : Rule Integer

partial
exprAtom : Rule Integer
exprAtom = (intLiteral <* commentSpace)
           <|> intLiteral <|> (paren expr)

partial
expr1 : Rule Integer
expr1 = map multInt exprAtom <*> (
          (((op "*") <* commentSpace) <|> (op "*"))
          *> exprAtom)

partial
exprMult : Rule Integer
exprMult = expr1 <|> exprAtom

partial
expr2 : Rule Integer
expr2 = map addInt exprMult <*> (
          (((op "+") <* commentSpace) <|> (op "+"))
          *> exprMult)

partial
exprAdd : Rule Integer
exprAdd = expr2 <|> exprMult

partial
expr3 : Rule Integer
expr3 = map subInt exprAdd <*> (
          (((op "-") <* commentSpace) <|> (op "-"))
          *> expr)

expr = expr3 <|> exprAdd

partial
test : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test s = parse expr (fst (lex expressionTokens s))

