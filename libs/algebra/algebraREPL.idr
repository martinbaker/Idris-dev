module Main

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

{-
Idris REPL does not input and display mathematical structures, such as
complex numbers or matricies, in mathematical notation. This code aims
to implement a REPL designed for mathematical structures.

to run:
cd Idris-dev/libs/algebra
idris -p contrib algebraREPL.idr
:exec
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
     (spaces, Comment),
     (comment, Comment)]

-- parser

-- from  Idris2/src/Parser/Support.idr 
public export
Rule : Type -> Type
Rule ty = Grammar (TokenData ExpressionToken) True ty

commentSpace : Rule Integer
commentSpace = terminal (\x => case tok x of
                           Comment s => Just 0
                           _ => Nothing)

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

||| Matches if this is an operator token and string matches, that is,
||| it is the required type of operator.
op : String -> Rule Integer
op s = terminal (\x => case tok x of
                           (Operator s1) => if s==s1 then Just 0 else Nothing
                           _ => Nothing)

addInt : Integer -> Integer -> Integer
addInt a b = a+b

subInt : Integer -> Integer -> Integer
subInt a b = a-b

multInt : Integer -> Integer -> Integer
multInt a b = a*b

expr : Rule Integer

factor : Rule Integer
factor = intLiteral <|> do
                openParen
                r <- expr
                closeParen
                pure r

term : Rule Integer
term = map multInt factor <*> (
          (op "*")
          *> factor)
       <|> factor

expr = map addInt term <*> (
          (op "+")
          *> term)
       <|> map subInt term <*> (
          (op "-")
          *> term)
       <|> term

eoi : Rule Integer
eoi = terminal (\x => case tok x of
                           EndInput => Just 0
                           _ => Nothing)


exprFull : Rule Integer
exprFull = expr <* eoi

processWhitespace : (List (TokenData ExpressionToken), Int, Int, String)
                  -> (List (TokenData ExpressionToken), Int, Int, String)
processWhitespace (x,l,c,s) = ((filter notComment x)++
                                      [MkToken l c EndInput],l,c,s) where
      notComment : TokenData ExpressionToken -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

calc : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
calc s = parse exprFull (fst (processWhitespace (lex expressionTokens s)))

lft : (ParseError (TokenData ExpressionToken)) -> IO ()
lft (Error s lst) = putStrLn ("error:"++s)

rht : (Integer, List (TokenData ExpressionToken)) -> IO ()
rht i = putStrLn ("right " ++ (show i))

main : IO ()
main = do
  putStr "alg>"
  x <- getLine
  either lft rht (calc x) -- eliminator for Either
