module ParserExample

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

{-
to run:
cd Idris-dev/libs/contrib
idris -p contrib parserExInfix.idr
     ____    __     _
-}

%default total

public export
data ExpressionToken = Number Integer
           | Operator String
           | OParen
           | CParen
           | EndInput

export
Show ExpressionToken where
  show (Number x) = "number " ++ show x
  show (Operator x) = "operator " ++ x
  show OParen = "("
  show CParen = ")"
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

expressionTokens : TokenMap ExpressionToken
expressionTokens =
    [(digits, \x => Number (toInt' x)),
     (operator, \x => Operator x),
     (is '(' ,\x => OParen),
     (is ')' ,\x => CParen)]

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

||| In order to try this out, here is a temporary function, this calls
||| parse which takes two parameters:
||| * The grammar (in this case intLiteral)
||| * The token list from the lexer.
test1 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test1 s = parse intLiteral (fst (lex expressionTokens s))

openParen : Rule Integer
openParen = terminal (\x => case tok x of
                           OParen => Just 0
                           _ => Nothing)

test2 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test2 s = parse openParen (fst (lex expressionTokens s))

test3 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test3 s = parse (map const openParen <*> intLiteral) (fst (lex expressionTokens s))

closeParen : Rule Integer
closeParen = terminal (\x => case tok x of
                           CParen => Just 0
                           _ => Nothing)

||| Matches if this is an operator token and string matches, that is,
||| it is the required type of operator.
op : String -> Rule Integer
op s = terminal (\x => case tok x of
                           (Operator s1) => if s==s1 then Just 0 else Nothing
                           _ => Nothing)

paren : Rule Integer -> Rule Integer
paren exp = openParen *> exp <* closeParen

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
exprAtom = intLiteral <|> (paren expr)

partial
expr1 : Rule Integer
expr1 = map multInt exprAtom <*> ((op "*") *> exprAtom)

partial
exprMult : Rule Integer
exprMult = expr1 <|> exprAtom

partial
expr2 : Rule Integer
expr2 = map addInt exprMult <*> ((op "+") *> exprMult)

partial
exprAdd : Rule Integer
exprAdd = expr2 <|> exprMult

partial
expr3 : Rule Integer
expr3 = map subInt exprAdd <*> ((op "-") *> expr)

expr = expr3 <|> exprAdd

partial
test : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test s = parse expr (fst (lex expressionTokens s))

