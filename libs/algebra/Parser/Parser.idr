module Idris.Parser

--import        Core.Options --**************
--import        Idris.Syntax --**************
import public Parser.Support
import        Parser.Lexer
import        Parser.FC
import public Parser.Syntax
--import        TTImp.TTImp --**************

import public Text.Parser
import        Data.List.Views

{-
to run:

cd Idris-dev/libs/algebra
idris -p algebra -p contrib Parser/Parser.idr
calc "65+2"
-}



%default covering

-- Forward declare since they're used in the parser
--********** FileName comes from Idris2/src/Core/FC.idr
topDecl : Rule (List PDecl)
collectDefs : List PDecl -> List PDecl --**************

-- Some context for the parser
public export
record ParseOpts where
  constructor MkParseOpts
  eqOK : Bool -- = operator is parseable
  withOK : Bool -- = with applications are parseable

peq : ParseOpts -> ParseOpts
peq = record { eqOK = True }

pnoeq : ParseOpts -> ParseOpts
pnoeq = record { eqOK = False }

export
pdef : ParseOpts
pdef = MkParseOpts True True

pnowith : ParseOpts
pnowith = MkParseOpts True False

export
plhs : ParseOpts
plhs = MkParseOpts False False

--********** FileName comes from Idris2/src/Core/FC.idr
atom : Rule PTerm
atom
    = do x <- constant
         pure (PPrimVal  x)
  <|> do keyword "Type"
         pure PType
  <|> do symbol "_"
         pure PImplicit
  <|> do symbol "?"
         pure PInfer
  <|> do x <- holeName
         pure (PHole  False x)
  <|> do symbol "%"
         exactIdent "MkWorld"
         pure (PPrimVal  WorldVal)
  <|> do symbol "%"
         exactIdent "World"
         pure (PPrimVal  WorldType)
  <|> do symbol "%"
         exactIdent "search"
         pure (PSearch  1000)
  <|> do x <- name
         pure (PRef  x)

{- cant use anything with blockAfter
whereBlock : Rule (List PDecl)
whereBlock
    = do keyword "where"
         ds <- blockAfter topDecl
         pure (collectDefs (concat ds))
-}

-- Expect a keyword, but if we get anything else it's a fatal error
commitKeyword : String -> Rule ()
commitKeyword req
    = do mustContinue (Just req)
         keyword req
         mustContinue Nothing

commitSymbol : String -> Rule ()
commitSymbol req
    = symbol req
       --<|> fatalError ("Expected '" ++ req ++ "'")
       <|> fail ("Expected '" ++ req ++ "'")

continueWith : String -> Rule ()
continueWith req
    = do mustContinue (Just req)
         symbol req

iOperator : Rule Name
iOperator
    = do n <- operator
         pure (UN n)
  <|> do symbol "`"
         n <- name
         symbol "`"
         pure n

data ArgType
    = ExpArg PTerm
    | ImpArg (Maybe Name) PTerm
    | WithArg PTerm

mutual
  appExpr : ParseOpts -> Rule PTerm
  appExpr q
      = -- case_
    --<|> 
    lazy
    --<|> if_
    --<|> doBlock
    <|> do f <- simpleExpr
           args <- many (argExpr q)
           pure (applyExpImp f args)
    <|> do op <- iOperator
           arg <- expr pdef
           pure (PPrefixOp  op arg)
    <|> fail "Expected 'case', 'if', 'do', application or operator expression"
    where
      applyExpImp : PTerm ->
                    List ArgType ->
                    PTerm
      applyExpImp f [] = f
      applyExpImp f (ExpArg exp :: args)
          = applyExpImp (PApp  f exp) args
      applyExpImp f (ImpArg n imp :: args)
          = applyExpImp (PImplicitApp  f n imp) args
      applyExpImp f (WithArg exp :: args)
          = applyExpImp (PWithApp  f exp) args

  argExpr : ParseOpts -> Rule ArgType
  argExpr q
      = do continue
           arg <- simpleExpr
           the (EmptyRule _) $ case arg of
                PHole _ n => pure (ExpArg (PHole True n))
                t => pure (ExpArg t)
    <|> do continue
           arg <- implicitArg
           pure (ImpArg (fst arg) (snd arg))
    <|> if withOK q
           then do symbol "|"
                   arg <- expr (record { withOK = False} q)
                   pure (WithArg arg)
           else fail "| not allowed here"

  implicitArg : Rule (Maybe Name, PTerm)
  implicitArg
      = do 
           symbol "{"
           x <- unqualifiedName
           (do symbol "="
               commit
               tm <- expr pdef
               symbol "}"
               pure (Just (UN x), tm))
             <|> (do symbol "}"
                     pure (Just (UN x), PRef  (UN x)))
    <|> do symbol "@{"
           commit
           tm <- expr pdef
           symbol "}"
           pure (Nothing, tm)

  opExpr : ParseOpts -> Rule PTerm
  opExpr q
      = do 
           l <- appExpr q
           (if eqOK q
               then do continue
                       symbol "="
                       r <- opExpr q
                       pure (POp  (UN "=") l r)
               else fail "= not allowed")
             <|>
             (do continue
                 op <- iOperator
                 middle <- location
                 r <- opExpr q
                 pure (POp  op l r))
               <|> pure l

  dpair : Rule PTerm
  dpair 
      = do x <- unqualifiedName
           symbol ":"
           ty <- expr pdef
           symbol "**"
           rest <- dpair <|> expr pdef
           pure (PDPair 
                        (PRef (UN x))
                        ty
                        rest)
    <|> do l <- expr pdef
           symbol "**"
           rest <- dpair<|> expr pdef
           pure (PDPair 
                        l
                        (PImplicit )
                        rest)

  bracketedExpr : Rule PTerm
  bracketedExpr
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do op <- iOperator
           e <- expr pdef
           continueWith ")"
           pure (PSectionL  op e)
      -- unit type/value
    <|> do continueWith ")"
           pure (PUnit )
      -- right section (1-tuple is just an expression)
    <|> do p <- dpair
           symbol ")"
           pure p
--    <|> do e <- expr pdef
--           (do op <- iOperator
--               symbol ")"
--               pure (PSectionR  e op)
--             <|>
--            -- all the other bracketed expressions
--            tuple e)

  getInitRange : List PTerm -> EmptyRule (PTerm, Maybe PTerm)
  getInitRange [x] = pure (x, Nothing)
  getInitRange [x, y] = pure (x, Just y)
  --getInitRange _ = fatalError "Invalid list range syntax" --*********************************
  getInitRange _ = fail "Invalid list range syntax"

  listRange : List PTerm -> Rule PTerm
  listRange xs
      = do symbol "]"
           --let fc = MkFC fname start end
           rstate <- getInitRange xs
           pure (PRangeStream (fst rstate) (snd rstate))
    <|> do y <- expr pdef
           symbol "]"
           --let fc = MkFC fname start end
           rstate <- getInitRange xs
           pure (PRange (fst rstate) (snd rstate) y)

{- use of sepBy1 is a problem
  listExpr : Rule PTerm
  listExpr
      = do ret <- expr pnowith
           symbol "|"
           conds <- sepBy1 (symbol ",") doAct
           symbol "]"
           pure (PComprehension  ret (concat conds))
    <|> do xs <- sepBy (symbol ",") (expr pdef)
           (do symbol ".."
               listRange xs)
             <|> (do symbol "]"
                     pure (PList  xs))
-}

  -- A pair, dependent pair, or just a single expression
  tuple : PTerm -> Rule PTerm
  tuple e
      = do rest <- some (do symbol ","
                            el <- expr pdef
                            pure (el))
           continueWith ")"
           pure (PPair e
                       (mergePairs rest))
     <|> do continueWith ")"
            pure (PBracketed e)
    where
      mergePairs : List PTerm -> PTerm
      mergePairs [] = PUnit
      mergePairs [exp] = exp
      mergePairs (exp :: rest)
          = PPair exp (mergePairs rest)

  simpleExpr : Rule PTerm
  simpleExpr
      = do x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr
           pure (PAs  (UN x) expr) -- PAs : Name -> (pattern : PTerm) -> PTerm
    <|> atom
    --<|> binder
    <|> rewrite_
    <|> record_
    <|> do symbol ".("
           commit
           e <- expr pdef
           symbol ")"
           pure (PDotted  e)
    <|> do symbol "`("
           e <- expr pdef
           symbol ")"
           pure (PQuote  e)
    <|> do 
           symbol "~"
           e <- simpleExpr
           pure (PUnquote  e)
    <|> do symbol "("
           bracketedExpr
--    <|> do symbol "["
--           listExpr
    <|> do symbol "%"; exactIdent "unifyLog"
           e <- expr pdef
           pure (PUnifyLog  e)

  multiplicity : EmptyRule (Maybe Integer)
  multiplicity
      = do c <- intLit
           pure (Just c)
--     <|> do symbol "&"
--            pure (Just 2) -- Borrowing, not implemented
    <|> pure Nothing

  getMult : Maybe Integer -> EmptyRule RigCount
  getMult (Just 0) = pure Rig0
  getMult (Just 1) = pure Rig1
  getMult Nothing = pure RigW
  --getMult _ = fatalError "Invalid multiplicity (must be 0 or 1)"
  getMult _ = fail "Invalid multiplicity (must be 0 or 1)" --*********************************

  pibindAll : PiInfo -> List (RigCount, Maybe Name, PTerm) ->
              PTerm -> PTerm
  pibindAll p [] scope = scope
  pibindAll p ((rig, n, ty) :: rest) scope
           = PPi rig p n ty (pibindAll p rest scope)

  bindList : Rule (List (RigCount, PTerm, PTerm))
  bindList
      = sepBy1 (symbol ",")
               (do rigc <- multiplicity
                   pat <- simpleExpr
                   ty <- option
                            PInfer
                            (do symbol ":"
                                opExpr pdef)
                   rig <- getMult rigc
                   pure (rig, pat, ty))

{- cant use anything with atEnd
  pibindList : Rule (List (RigCount, Maybe Name, PTerm))
  pibindList
       = do rigc <- multiplicity
            ns <- sepBy1 (symbol ",") unqualifiedName
            symbol ":"
            ty <- expr pdef
            atEnd
            rig <- getMult rigc
            pure (map (\n => (rig, Just (UN n), ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rigc <- multiplicity
                    n <- name
                    symbol ":"
                    ty <- expr pdef
                    rig <- getMult rigc
                    pure (rig, Just n, ty))
-}

  bindSymbol : Rule PiInfo
  bindSymbol
      = do symbol "->"
           pure Explicit
    <|> do symbol "=>"
           pure AutoImplicit

{- pibindAll had to be removed
  explicitPi : Rule PTerm
  explicitPi
      = do 
           symbol "("
           binders <- pibindList
           symbol ")"
           exp <- bindSymbol
           scope <- typeExpr pdef
           pure (pibindAll  exp binders scope)

  autoImplicitPi : Rule PTerm
  autoImplicitPi
      = do 
           symbol "{"
           keyword "auto"
           commit
           binders <- pibindList
           symbol "}"
           symbol "->"
           scope <- typeExpr pdef
           pure (pibindAll  AutoImplicit binders scope)

  forall_ : Rule PTerm
  forall_
      = do 
           keyword "forall"
           commit
           n
           ns <- sepBy1 (symbol ",") unqualifiedName
           n
           --let nfc = MkFC fname nstart nend
           let binders = map (\n => (Rig0, Just (UN n), PImplicit)) ns
           symbol "."
           scope <- typeExpr pdef
           pure (pibindAll  Implicit binders scope)

  implicitPi : Rule PTerm
  implicitPi
      = do 
           symbol "{"
           binders <- pibindList
           symbol "}"
           symbol "->"
           scope <- typeExpr pdef
           pure (pibindAll  Implicit binders scope)
-}

  lam : Rule PTerm
  lam
      = do 
           symbol "\\"
           binders <- bindList
           symbol "=>"
           mustContinue Nothing
           scope <- expr pdef
           pure (bindAll  binders scope)
     where
       bindAll : List (RigCount, PTerm, PTerm) -> PTerm -> PTerm
       bindAll [] scope = scope
       bindAll ((rig, pat, ty) :: rest) scope
           = PLam rig Explicit pat ty (bindAll rest scope)

{- uses block which requires indents
  letBinder : Rule (RigCount, PTerm, PTerm, List PClause)
  letBinder
      = do 
           rigc <- multiplicity
           pat <- expr plhs
           symbol "="
           val <- expr pnowith
           alts <- block patAlt
           rig <- getMult rigc
           pure (rig, pat, val, alts)
-}

  buildLets :
              List (RigCount, PTerm, PTerm, List PClause) ->
              PTerm -> PTerm
  buildLets [] sc = sc
  buildLets ((rig, pat, val, alts) :: rest) sc
      = PLet rig pat PImplicit val
                 (buildLets rest sc) alts

  buildDoLets : 
                List (RigCount, PTerm, PTerm, List PClause) ->
                List PDo
  buildDoLets [] = []
  buildDoLets ((rig, PRef (UN n), val, []) :: rest)
      = if lowerFirst n
               then DoLet (UN n) rig val :: buildDoLets rest
               else DoLetPat (PRef (UN n)) val []
                         :: buildDoLets rest
  buildDoLets ((rig, pat, val, alts) :: rest)
      = DoLetPat pat val alts :: buildDoLets rest

{- uses letbinder
  let_ : Rule PTerm
  let_ 
      = do keyword "let"
           res <- nonEmptyBlock letBinder
           commitKeyword "in"
           scope <- typeExpr pdef
           pure (buildLets res scope)

    <|> do 
           keyword "let"
           commit
           ds <- nonEmptyBlock topDecl
           commitKeyword indents "in"
           scope <- typeExpr pdef
           pure (PLocal  (collectDefs (concat ds)) scope)
-}
{- uses block which requires indents
  case_ : Rule PTerm
  case_
      = do 
           keyword "case"
           scr <- expr pdef
           commitKeyword indents "of"
           alts <- block caseAlt
           pure (PCase  scr alts)
-}
{- uses caseRHS
  caseAlt : Rule PClause
  caseAlt
      = do 
           lhs <- opExpr plhs
           caseRHS lhs
-}
{- cant use anything with atEnd
  caseRHS : PTerm -> Rule PClause
  caseRHS lhs
      = do symbol "=>"
           mustContinue Nothing
           rhs <- expr pdef
           atEnd
           pure (MkPatClause  lhs rhs [])
    <|> do keyword "impossible"
           atEnd
           pure (MkImpossible  lhs)

  if_ : Rule PTerm
  if_
      = do 
           keyword "if"
           x <- expr pdef
           commitKeyword "then"
           t <- expr pdef
           commitKeyword "else"
           e <- expr pdef
           atEnd
           pure (PIfThenElse  x t e)
-}

  record_ : Rule PTerm
  record_
      = do 
           keyword "record"
           commit
           symbol "{"
           fs <- sepBy1 (symbol ",") field
           symbol "}"
           pure (PUpdate  fs)

  field : Rule PFieldUpdate
  field
      = do path <- sepBy1 (symbol "->") unqualifiedName
           upd <- (do symbol "="; pure PSetField)
                      <|>
                  (do symbol "$="; pure PSetFieldApp)
           val <- opExpr plhs
           pure (upd path val)

  rewrite_ : Rule PTerm
  rewrite_
      = do keyword "rewrite"
           rule <- expr pdef
           commitKeyword "in"
           tm <- expr pdef
           pure (PRewrite  rule tm)

{- uses block which requires indents
  doBlock : Rule PTerm
  doBlock
      = do 
           keyword "do"
           actions <- block doAct
           pure (PDoBlock  (concat actions))
-}

  lowerFirst : String -> Bool
  lowerFirst "" = False
  lowerFirst str = assert_total (isLower (strHead str))

  validPatternVar : Name -> EmptyRule ()
  validPatternVar (UN n)
      = if lowerFirst n then pure ()
                        else fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

{- cant use anything with atEnd or block
  doAct : Rule (List PDo)
  doAct
      = do n <- name
           -- If the name doesn't begin with a lower case letter, we should
           -- treat this as a pattern, so fail
           validPatternVar n
           symbol "<-"
           val <- expr pdef
           atEnd
           pure [DoBind  n val]
    <|> do keyword "let"
           res <- block letBinder
           atEnd
           pure (buildDoLets res)
    <|> do keyword "let"
           res <- block topDecl
           atEnd
           pure [DoLetLocal  (concat res)]
    <|> do 
           keyword "rewrite"
           rule <- expr pdef
           atEnd
           pure [DoRewrite  rule]
    <|> do 
           e <- expr plhs
           (do atEnd
               pure [DoExp  e])
             <|> (do symbol "<-"
                     val <- expr pnowith
                     alts <- block patAlt
                     atEnd
                     pure [DoBindPat  e val alts])
-}
{- uses caseAlt
  patAlt : Rule PClause
  patAlt
      = do symbol "|"
           caseAlt
-}

  lazy : Rule PTerm
  lazy
      = do 
           keyword "Lazy"
           tm <- simpleExpr
           pure (PDelayed  LLazy tm)
    <|> do 
           keyword "Inf"
           tm <- simpleExpr
           pure (PDelayed  LInf tm)
    <|> do 
           keyword "Delay"
           tm <- simpleExpr
           pure (PDelay  tm)
    <|> do 
           keyword "Force"
           tm <- simpleExpr
           pure (PForce  tm)

{- uses let_
  binder : Rule PTerm
  binder
      = let_
    <|> autoImplicitPi
    <|> forall_
    <|> implicitPi
    <|> explicitPi
    <|> lam
-}

  typeExpr : ParseOpts -> Rule PTerm
  typeExpr q
      = do 
           arg <- opExpr q
           (do continue
               rest <- some (do exp <- bindSymbol
                                op <- opExpr pdef
                                pure (exp, op))
               pure (mkPi arg rest))
             <|> pure arg
    where
      mkPi : PTerm -> List (PiInfo, PTerm) -> PTerm
      mkPi arg [] = arg
      mkPi arg ((exp, a) :: as)
            = PPi  RigW exp Nothing arg
                  (mkPi a as)

  export
  expr : ParseOpts -> Rule PTerm
  expr = typeExpr

visOption : Rule Visibility
visOption
    = do keyword "public"
         keyword "export"
         pure Public
  <|> do keyword "export"
         pure Export
  <|> do keyword "private"
         pure Private

visibility : EmptyRule Visibility
visibility
    = visOption
  <|> pure Private

{- cant use anything with atEnd
tyDecl : Rule PTypeDecl
tyDecl
    = do 
         n <- name
         symbol ":"
--         mustWork $ -- mustwork is not in Idris 1
--            do ty <- expr pdef
--               atEnd
--               pure (MkPTy  n ty)
         ty <- expr pdef
         atEnd
         pure (MkPTy  n ty)

mutual
  parseRHS : (withArgs : Nat) ->
             (lhs : PTerm) -> Rule PClause
  parseRHS withArgslhs
       = do symbol "="
--            mustWork $
--              do rhs <- expr pdef
--                 ws <- option [] (whereBlock fname col)
--                 atEnd
--                 pure (MkPatClause  lhs rhs ws)
            rhs <- expr pdef
            ws <- option [] whereBlock
            atEnd
            pure (MkPatClause  lhs rhs ws)
     <|> do keyword "with"
            w
            symbol "("
            wval <- bracketedExpr
            ws <- nonEmptyBlock (clause (S withArgs))
            pure (MkWithClause  lhs wval ws)
     <|> do keyword "impossible"
            atEnd
            pure (MkImpossible  lhs)


  clause : Nat -> Rule PClause
  clause withArgs
      = do 
           lhs <- expr plhs
           extra <- many parseWithArg
           if (withArgs /= length extra)
              --then fatalError "Wrong number of 'with' arguments" --***************************
              then fail "Wrong number of 'with' arguments"
              else parseRHS withArgs (applyArgs lhs extra)
    where
      applyArgs : PTerm -> List PTerm -> PTerm
      applyArgs f [] = f
      applyArgs f (a :: args) = applyArgs (PApp f a) args

      parseWithArg : Rule PTerm
      parseWithArg
          = do symbol "|"
               tm <- expr plhs
               pure tm
-}

mkTyConType : List Name -> PTerm
mkTyConType [] = PType
mkTyConType (x :: xs)
   = PPi Rig1 Explicit Nothing (PType) (mkTyConType xs)

mkDataConType : PTerm -> List ArgType -> PTerm
mkDataConType ret [] = ret
mkDataConType ret (ExpArg x :: xs)
    = PPi Rig1 Explicit Nothing x (mkDataConType ret xs)
mkDataConType ret (ImpArg n (PRef x) :: xs)
    = if n == Just x
         then PPi Rig1 Implicit n PType
                          (mkDataConType ret xs)
         else PPi Rig1 Implicit n (PRef x)
                          (mkDataConType ret xs)
mkDataConType ret (ImpArg n x :: xs)
    = PPi Rig1 Implicit n x (mkDataConType ret xs)
mkDataConType ret (WithArg a :: xs)
    = PImplicit -- This can't happen because we parse constructors without
                   -- withOK set

{-
simpleCon : PTerm -> Rule PTypeDecl
simpleCon ret
    = do 
         cname <- name
         params <- many (argExpr plhs)
         atEnd
         pure (MkPTy cname (mkDataConType ret params))

simpleData : Name -> Rule PDataDecl
simpleData n
    = do params <- many name
         --let tyfc = MkFC tyend
         symbol "="
         let conRetTy = papply (PRef n)
                           (map PRef params)
         cons <- sepBy1 (symbol "|")
                        (simpleCon conRetTy)
         pure (MkPData  n
                       (mkTyConType params) [] cons)
-}

dataOpt : Rule DataOpt
dataOpt
    = do exactIdent "noHints"
         pure NoHints
  <|> do exactIdent "uniqueSearch"
         pure UniqueSearch
  <|> do exactIdent "search"
         ns <- some name
         pure (SearchBy ns)

{- cant use anything with blockAfter
dataBody : Name -> PTerm ->
           EmptyRule PDataDecl
dataBody n ty
    = do atEnd
         pure (MkPLater  n ty)
  <|> do keyword "where"
         opts <- option [] (do symbol "["
                               dopts <- sepBy1 (symbol ",") dataOpt
                               symbol "]"
                               pure dopts)
         cs <- blockAfter tyDecl
         pure (MkPData  n ty opts cs)
-}
{- dataBody
gadtData : Int -> Name -> Rule PDataDecl
gadtData  mincol n
    = do symbol ":"
         commit
         ty <- expr pdef
         dataBody mincol n ty

dataDeclBody : Rule PDataDecl
dataDeclBody
    = do 
         col <- column
         keyword "data"
         n <- name
         simpleData n
           <|> gadtData col n

dataDecl : Rule PDecl
dataDecl
    = do 
         vis <- visibility
         dat <- dataDeclBody
         pure (PData  vis dat)
-}

stripBraces : String -> String
stripBraces str = pack (drop '{' (reverse (drop '}' (reverse (unpack str)))))
  where
    drop : Char -> List Char -> List Char
    drop c [] = []
    drop c (c' :: xs) = if c == c' then drop c xs else c' :: xs

onoff : Rule Bool
onoff
   = do exactIdent "on"
        pure True
 <|> do exactIdent "off"
        pure False

extension : Rule LangExt
extension
    = do exactIdent "Borrowing"
         pure Borrowing

{- cant use anything with atEnd
directive : Rule Directive
directive
    = do exactIdent "hide"
         n <- name
         atEnd
         pure (Hide n)
--   <|> do exactIdent "hide_export"
--          n <- name
--          atEnd
--          pure (Hide True n)
  <|> do exactIdent "logging"
         lvl <- intLit
         atEnd
         pure (Logging (cast lvl))
  <|> do exactIdent "auto_lazy"
         b <- onoff
         atEnd
         pure (LazyOn b)
  <|> do exactIdent "pair"
         ty <- name
         f <- name
         s <- name
         atEnd
         pure (PairNames ty f s)
  <|> do keyword "rewrite"
         eq <- name
         rw <- name
         atEnd
         pure (RewriteName eq rw)
  <|> do exactIdent "integerLit"
         n <- name
         atEnd
         pure (PrimInteger n)
  <|> do exactIdent "stringLit"
         n <- name
         atEnd
         pure (PrimString n)
  <|> do exactIdent "charLit"
         n <- name
         atEnd
         pure (PrimChar n)
  <|> do exactIdent "name"
         n <- name
         ns <- sepBy1 (symbol ",") unqualifiedName
         atEnd
         pure (Names n ns)
  <|> do exactIdent "start"
         e <- expr pdef
         atEnd
         pure (StartExpr e)
  <|> do exactIdent "allow_overloads"
         n <- name
         atEnd
         pure (Overloadable n)
--  <|> do exactIdent "language"
--         e <- extension
--         atEnd
--         pure (Extension e)
-}

--fix : Rule Fixity--*****************************
fix : Rule Parser.Syntax.Fixity
fix
    = do keyword "infixl"; pure InfixL
  <|> do keyword "infixr"; pure InfixR
  <|> do keyword "infix"; pure Infix
  <|> do keyword "prefix"; pure Prefix

{-
namespaceHead : Rule (List String)
namespaceHead
    = do keyword "namespace"
         commit
         ns <- namespace_ -- namespace_ uses col ****************************
         pure ns

namespaceDecl : Rule PDecl
namespaceDecl
    = do ns <- namespaceHead
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         pure (PNamespace  ns (concat ds))
-}
{-
mutualDecls : Rule PDecl
mutualDecls
    = do 
         keyword "mutual"
         commit
         ds <- assert_total (nonEmptyBlock topDecl)
         pure (PMutual  (concat ds))
-}
{- nonemptyblock
paramDecls : Rule PDecl
paramDecls
    = do keyword "parameters"
         commit
         symbol "("
         ps <- sepBy (symbol ",")
                     (do x <- unqualifiedName
                         symbol ":"
                         ty <- typeExpr pdef
                         pure (UN x, ty))
         symbol ")"
         ds <- assert_total (nonEmptyBlock topDecl)
         pure (PParameters  ps (collectDefs (concat ds)))
-}

fnOpt : Rule PFnOpt
fnOpt
    = do keyword "partial"
         pure $ IFnOpt PartialOK
  <|> do keyword "total"
         pure $ IFnOpt Total
  <|> do keyword "covering"
         pure $ IFnOpt Covering

{- uses block which requires indents
fnDirectOpt : Rule PFnOpt
fnDirectOpt
    = do exactIdent "hint"
         pure $ IFnOpt (Hint True)
  <|> do exactIdent "globalhint"
         pure $ IFnOpt (GlobalHint False)
  <|> do exactIdent "defaulthint"
         pure $ IFnOpt (GlobalHint True)
  <|> do exactIdent "inline"
         pure $ IFnOpt Inline
  <|> do exactIdent "extern"
         pure $ IFnOpt ExternFn
  <|> do exactIdent "macro"
         pure $ IFnOpt Macro
  <|> do exactIdent "foreign"
         cs <- block (expr pdef)
         pure $ PForeign cs
-}
{- fndirectopt
visOpt : Rule (Either Visibility PFnOpt)
visOpt
    = do vis <- visOption
         pure (Left vis)
  <|> do tot <- fnOpt
         pure (Right tot)
  <|> do symbol "%"
         opt <- fnDirectOpt
         pure (Right opt)
-}

getVisibility : Maybe Visibility -> List (Either Visibility PFnOpt) ->
                EmptyRule Visibility
getVisibility Nothing [] = pure Private
getVisibility (Just vis) [] = pure vis
getVisibility Nothing (Left x :: xs) = getVisibility (Just x) xs
getVisibility (Just vis) (Left x :: xs)
   --= fatalError "Multiple visibility modifiers" --************************************
   = fail "Multiple visibility modifiers"
getVisibility v (_ :: xs) = getVisibility v xs

getRight : Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right v) = Just v

constraints : EmptyRule (List (Maybe Name, PTerm))
constraints
    = do tm <- appExpr pdef
         symbol "=>"
         more <- constraints
         pure ((Nothing, tm) :: more)
  <|> do symbol "("
         n <- name
         symbol ":"
         tm <- expr pdef
         symbol ")"
         symbol "=>"
         more <- constraints
         pure ((Just n, tm) :: more)
  <|> pure []

implBinds : EmptyRule (List (Name, RigCount, PTerm))
implBinds
    = do symbol "{"
         m <- multiplicity
         rig <- getMult m
         n <- name
         symbol ":"
         tm <- expr pdef
         symbol "}"
         symbol "->"
         more <- implBinds
         pure ((n, rig, tm) :: more)
  <|> pure []

ifaceParam : Rule (Name, PTerm)
ifaceParam
    = do symbol "("
         n <- name
         symbol ":"
         tm <- expr pdef
         symbol ")"
         pure (n, tm)
  <|> do n <- name
         pure (n, PInfer )

{- cant use anything with blockAfter
ifaceDecl : Rule PDecl
ifaceDecl
    = do vis <- visibility
         keyword "interface"
         commit
         cons <- constraints
         n <- name
         params <- many (ifaceParam)
         det <- option [] (do symbol "|"
                              sepBy (symbol ",") name)
         keyword "where"
         dc <- option Nothing (do exactIdent "constructor"
                                  n <- name
                                  pure (Just n))
         body <- assert_total (blockAfter topDecl)
         pure (PInterface 
                      vis cons n params det dc (collectDefs (concat body)))

implDecl : Rule PDecl
implDecl
    = do vis <- visibility
         option () (keyword "implementation")
         iname <- option Nothing (do symbol "["
                                     iname <- name
                                     symbol "]"
                                     pure (Just iname))
         impls <- implBinds
         cons <- constraints
         n <- name
         params <- many simpleExpr
         body <- optional (do keyword "where"
                              blockAfter topDecl)
         --atEnd
         pure (PImplementation 
                         vis Single impls cons n params iname
                         (map (collectDefs . concat) body))
-}

{- cant use anything with atEnd
fieldDecl : Rule (List PField)
fieldDecl
      = do symbol "{"
           commit
           fs <- fieldBody Implicit
           symbol "}"
           atEnd
           pure fs
    <|> do fs <- fieldBody Explicit
           atEnd
           pure fs
  where
    fieldBody : PiInfo -> Rule (List PField)
    fieldBody p
        = do m <- multiplicity
             rigin <- getMult m
             let rig = case rigin of
                            Rig0 => Rig0
                            _ => Rig1
             ns <- sepBy1 (symbol ",") name
             symbol ":"
             ty <- expr pdef
             pure (map (\n => MkField 
                                      rig p n ty) ns)

recordDecl : Rule PDecl
recordDecl
    = do vis <- visibility
         col <- column
         keyword "record"
         commit
         n <- name
         params <- many ifaceParam
         keyword "where"
         dcflds <- blockWithOptHeaderAfter col ctor (fieldDecl fname)
         pure (PRecord 
                       vis n params (fst dcflds) (concat (snd dcflds)))
  where
  ctor : Rule Name
  ctor = do exactIdent "constructor"
                n <- name
                atEnd
                pure n
-}
{-visOpt
claim : Rule PDecl
claim 
    = do visOpts <- many visOpt
         vis <- getVisibility Nothing visOpts
         let opts = mapMaybe getRight visOpts
         m <- multiplicity
         rig <- getMult m
         cl <- tyDecl
         pure (PClaim  rig vis opts cl)
-}
{- clause
definition : Rule PDecl
definition
    = do nd <- clause 0
         pure (PDef  [nd])
-}

fixDecl : Rule (List PDecl)
fixDecl
    = do 
         fixity <- fix
         commit
         prec <- intLit
         ops <- sepBy1 (symbol ",") iOperator
         pure (map (PFixity  fixity (cast prec)) ops)

{-
directiveDecl : Rule PDecl
directiveDecl
    = do 
         symbol "%"
         (do d <- directive
             pure (PDirective  d))
           <|>
          (do exactIdent "runElab"
              tm <- expr pdef
              atEnd
              pure (PReflect  tm))
-}

-- Declared at the top
-- topDecl : Rule (List PDecl)
topDecl = fail "Couldn't parse declaration"
{-
    = do d <- dataDecl
         pure [d]
  <|> do d <- claim
         pure [d]
  <|> do d <- definition
         pure [d]
  <|> fixDecl
  <|> do d <- ifaceDecl
         pure [d]
  <|> do d <- implDecl
         pure [d]
  <|> do d <- recordDecl
         pure [d]
  <|> do d <- namespaceDecl
         pure [d]
  <|> do d <- mutualDecls
         pure [d]
  <|> do d <- paramDecls
         pure [d]
  <|> do d <- directiveDecl
         pure [d]
--  <|> do dstr <- terminal "Expected CG directive"
--                          (\x => case tok x of
--                                      CGDirective d => Just d
--                                      _ => Nothing)
--         let cgrest = span isAlphaNum dstr
--         pure [PDirective 
--                (CGAction (fst cgrest) (stripBraces (trim (snd cgrest))))]
  --<|> fatalError "Couldn't parse declaration" --****************************************
  <|> fail "Couldn't parse declaration"
-}

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses into one definition. This might mean merging two
-- functions which are different, if there are forward declarations,
-- but we'll split them in Desugar.idr. We can't do this now, because we
-- haven't resolved operator precedences yet.
-- Declared at the top.
-- collectDefs : List PDecl -> List PDecl
collectDefs [] = []
collectDefs (PDef cs :: ds)
    = let (cs', rest) = spanMap isClause ds in
          PDef (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : PDecl -> Maybe (List PClause)
    isClause (PDef cs)
        = Just cs
    isClause _ = Nothing
collectDefs (PNamespace ns nds :: ds)
    = PNamespace ns (collectDefs nds) :: collectDefs ds
collectDefs (PMutual nds :: ds)
    = PMutual (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

{- cant use anything with atEnd
export
import_ : Rule Import
import_ 
    = do keyword "import"
         reexp <- option False (do keyword "public"
                                   pure True)
         ns <- namespace_ -- namespace_ uses col ****************************
         nsAs <- option ns (do exactIdent "as"
                               namespace_)
         atEnd
         pure (MkImport  reexp ns nsAs)
-}

{-
export
prog : EmptyRule Module
prog
    = do nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_) -- namespace_ uses col ****************************
         imports <- block import_
         ds <- block topDecl
         pure (MkModule 
                        nspace imports (collectDefs (concat ds)))

export
progHdr : EmptyRule Module
progHdr
    = do nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_) -- namespace_ uses col ****************************
         imports <- block import_
         pure (MkModule 
                        nspace imports [])
-}

parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "tc"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute
   <|> do exactIdent "exec"
          pure Execute

setVarOption : Rule REPLOpt
setVarOption
    = do exactIdent "eval"
         mode <- parseMode
         pure (EvalMode mode)
  <|> do exactIdent "editor"
         e <- unqualifiedName
         pure (Editor e)
  <|> do exactIdent "cg"
         c <- unqualifiedName
         pure (CG c)

setOption : Bool -> Rule REPLOpt
setOption set
    = do exactIdent "showimplicits"
         pure (ShowImplicits set)
  <|> do exactIdent "shownamespace"
         pure (ShowNamespace set)
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  --<|> if set then setVarOption else fatalError "Unrecognised option" --************************
  <|> if set then setVarOption else fail "Unrecognised option"

replCmd : List String -> Rule ()
replCmd [] = fail "Unrecognised command"
replCmd (c :: cs)
    = exactIdent c
  <|> replCmd cs

export
editCmd : Rule EditCmd
editCmd
    = do replCmd ["typeat"]
         line <- intLit
         col <- intLit
         n <- name
         pure (TypeAt (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["cs"]
         line <- intLit
         col <- intLit
         n <- name
         pure (CaseSplit (fromInteger line) (fromInteger col) n)
  <|> do replCmd ["ac"]
         line <- intLit
         n <- name
         pure (AddClause (fromInteger line) n)
  <|> do replCmd ["ps", "proofsearch"]
         line <- intLit
         n <- name
         pure (ExprSearch (fromInteger line) n [] False)
  <|> do replCmd ["psall"]
         line <- intLit
         n <- name
         pure (ExprSearch (fromInteger line) n [] True)
  <|> do replCmd ["gd"]
         line <- intLit
         n <- name
         pure (GenerateDef (fromInteger line) n)
  <|> do replCmd ["ml", "makelemma"]
         line <- intLit
         n <- name
         pure (MakeLemma (fromInteger line) n)
  <|> do replCmd ["mc", "makecase"]
         line <- intLit
         n <- name
         pure (MakeCase (fromInteger line) n)
  <|> do replCmd ["mw", "makewith"]
         line <- intLit
         n <- name
         pure (MakeWith (fromInteger line) n)
  --<|> fatalError "Unrecognised command" --*****************************************
  <|> fail "Unrecognised command"

nonEmptyCommand : Rule REPLCmd
nonEmptyCommand
    = do symbol ":"; replCmd ["t", "type"]
         tm <- expr pdef --"(interactive)"
         pure (Check tm)
  <|> do symbol ":"; replCmd ["printdef"]
         n <- name
         pure (PrintDef n)
  <|> do symbol ":"; replCmd ["s", "search"]
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; replCmd ["q", "quit", "exit"]
         pure Quit
  <|> do symbol ":"; exactIdent "set"
         opt <- setOption True
         pure (SetOpt opt)
  <|> do symbol ":"; exactIdent "unset"
         opt <- setOption False
         pure (SetOpt opt)
  <|> do symbol ":"; replCmd ["c", "compile"]
         n <- unqualifiedName
         tm <- expr pdef --"(interactive)"
         pure (Compile tm n)
  <|> do symbol ":"; exactIdent "exec"
         tm <- expr pdef --"(interactive)"
         pure (Exec tm)
  <|> do symbol ":"; replCmd ["r", "reload"]
         pure Reload
  <|> do symbol ":"; replCmd ["e", "edit"]
         pure Edit
  <|> do symbol ":"; replCmd ["miss", "missing"]
         n <- name
         pure (Missing n)
  <|> do symbol ":"; keyword "total"
         n <- name
         pure (Total n)
  <|> do symbol ":"; replCmd ["log", "logging"]
         i <- intLit
         pure (SetLog (fromInteger i))
  <|> do symbol ":"; replCmd ["m", "metavars"]
         pure Metavars
  <|> do symbol ":"; replCmd ["version"]
         pure ShowVersion
  <|> do symbol ":"; cmd <- editCmd
         pure (Editing cmd)
  <|> do tm <- expr pdef --"(interactive)" init
         pure (Eval tm)

export
command : EmptyRule REPLCmd
command
    = do eoi
         pure NOP
  <|> nonEmptyCommand

eoi2 : Rule Integer
eoi2 = terminal (\x => case tok x of
                           EndInput => Just 0
                           _ => Nothing)

||| works for:
||| calc "1"
||| but does not yet detect operators like:
||| calc "65+2"
onlyExpr : Rule PTerm
onlyExpr = simpleExpr <* eoi2

-- simpleExpr : Rule PTerm
calc : String -> Either (ParseError (TokenData Token))
                        (PTerm, List (TokenData Token))
calc s = parse onlyExpr (fst (lexAlg s))
