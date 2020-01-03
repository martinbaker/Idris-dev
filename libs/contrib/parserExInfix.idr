module ParserExample

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser

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
*parserEx> lex expressionTokens "1+2"
([MkToken 0 0 (Number 1),
  MkToken 0
          (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "1" of
             (incol, "") => c + cast (length incol)
             (incol, b) => cast (length incol))
          (Operator "+"),
  MkToken 0
          (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "+" of
             (incol, "") => c + cast (length incol)
             (incol, b) => cast (length incol))
          (Number 2)],
 0,
 case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "2" of
   (incol, "") => c + cast (length incol)
   (incol, b) => cast (length incol),
 getString (MkStrLen "" 0)) : (List (TokenData ExpressionToken),
                               Int,
                               Int,
                               String)
*parserEx>
The lexer uses potentially infinite data structures. It has recursive arguments (codata type) so code is lazy.
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

{-
parser
------
To run our parser we call 'doParse'. This requires the output from the lexer (a list of tokens) and a Grammar.
doParse : {c : Bool} ->
          (commit : Bool) -> (xs : List tok) -> (act : Grammar tok c ty) ->
          ParseResult xs c ty
So we need to define the Grammar for our parser
||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
public export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : String -> (tok -> Maybe a) -> Grammar tok True a
     NextIs : String -> (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()
     Fail : Bool -> String -> Grammar tok c ty
     Commit : Grammar tok False ()
     MustWork : Grammar tok c a -> Grammar tok c a
     SeqEat : Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : {c1, c2 : Bool} ->
                Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : {c1, c2 : Bool} ->
           Grammar tok c1 ty -> Grammar tok c2 ty ->
           Grammar tok (c1 && c2) ty
-}
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

{-
In order to try this out, here is a temporary function, this calls
parse which takes two parameters:
* The grammar (in this case intLiteral)
* The token list from the lexer.
-}
test1 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test1 s = parse intLiteral (fst (lex expressionTokens s))

{-
As required, if we pass it a string which is a number literal then it will return the
number in the 'Right' option.
*parserEx> test1 "123"
Right (123, []) : Either (ParseError (TokenData ExpressionToken))
                         (Integer, List (TokenData ExpressionToken))
If we pass it a string which is not a number literal then it will return an
error message.
*parserEx> test1 "a"
Left (Error "End of input"
            []) : Either (ParseError (TokenData ExpressionToken))
                         (Integer, List (TokenData ExpressionToken))
If we pass it a number followed by something else, then it will still be
successful, this is because we are not specifically checking for end-of-file.
*parserEx> test1 "123a"
Right (123, []) : Either (ParseError (TokenData ExpressionToken))
                         (Integer, List (TokenData ExpressionToken))
*parserEx> 
-}

{-
||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export
terminal : (tok -> Maybe a) -> Grammar tok True a
terminal = Terminal
-}

openParen : Rule Integer
openParen = terminal (\x => case tok x of
                           OParen => Just 0
                           _ => Nothing)

test2 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test2 s = parse openParen (fst (lex expressionTokens s))

{-
*parserEx> test2 "("
Right (0, []) : Either (ParseError (TokenData ExpressionToken))
                       (Integer, List (TokenData ExpressionToken))
*parserEx> test2 "123"
Left (Error "Unrecognised token"
            [MkToken 0
                     0
                     (Number 123)]) : Either (ParseError (TokenData ExpressionToken))
                                             (Integer,
                                              List (TokenData ExpressionToken))
*parserEx> 
-}

test3 : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test3 s = parse (map const openParen <*> intLiteral) (fst (lex expressionTokens s))

{-
*parserEx> test3 "(123"
Right (0, []) : Either (ParseError (TokenData ExpressionToken))
                       (Integer, List (TokenData ExpressionToken))
*parserEx> test3 "(("
Left (Error "Unrecognised token"
            [MkToken 0
                     (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n')))
                                 "(" of
                        (incol, "") => c + cast (length incol)
                        (incol, b) => cast (length incol))
                     OParen]) : Either (ParseError (TokenData ExpressionToken))
                                       (Integer, List (TokenData ExpressionToken))
*parserEx> test3 "123"
Left (Error "Unrecognised token"
            [MkToken 0
                     0
                     (Number 123)]) : Either (ParseError (TokenData ExpressionToken))
                                             (Integer,
                                              List (TokenData ExpressionToken))
*parserEx> test3 "123("
Left (Error "Unrecognised token"
            [MkToken 0 0 (Number 123),
             MkToken 0
                     (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n')))
                                 "321" of
                        (incol, "") => c + cast (length incol)
                        (incol, b) => cast (length incol))
                     OParen]) : Either (ParseError (TokenData ExpressionToken))
                                       (Integer, List (TokenData ExpressionToken))
*parserEx> -}

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

export
add : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
add x y z = map addInt (x <* y) <*> z

subInt : Integer -> Integer -> Integer
subInt a b = a-b

export
sub : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
sub x y z = map subInt (x <* y) <*> z


multInt : Integer -> Integer -> Integer
multInt a b = a*b

export
mult : Grammar tok c1 Integer ->
      Grammar tok c2 Integer ->
      Grammar tok c3 Integer ->
      Grammar tok ((c1 || c2) || c3) Integer
mult x y z = map multInt (x <* y) <*> z

expr : Rule Integer
expr = (add expr (op "+") expr)
       <|> (sub expr (op "-") expr)
       <|> (mult expr (op "*") expr)
       <|> intLiteral <|> (paren expr)

{-
*parserEx> parse expr (fst (lex expressionTokens "(1)"))
Right (1, []) : Either (ParseError (TokenData ExpressionToken))
                       (Integer, List (TokenData ExpressionToken))
*parserEx>
-}

{-
parse : (act : Grammar tok c ty) -> (xs : List tok)
parse intLiteral (fst (lex expressionTokens "1"))
-}

{-
*parserEx> parse expr (fst (lex expressionTokens "1+2"))
Right (1,
       [MkToken 0
                (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "1" of
                   (incol, "") => c + cast (length incol)
                   (incol, b) => cast (length incol))
                (Operator "+"),
        MkToken 0
                (case fspan (\ARG => not (intToBool (prim__eqChar ARG '\n'))) "+" of
                   (incol, "") => c + cast (length incol)
                   (incol, b) => cast (length incol))
                (Number 2)]) : Either (ParseError (TokenData ExpressionToken))
                                      (Integer, List (TokenData ExpressionToken))
*parserEx> 
-}

partial
test : String -> Either (ParseError (TokenData ExpressionToken))
                        (Integer, List (TokenData ExpressionToken))
test s = parse expr (fst (lex expressionTokens s))

