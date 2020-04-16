module Parser.displayGrammar

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


%access public export

-------------------------------------------------------------------

--outputGrammar : Grammar (TokenData Token) consume PTerm -> IO ()
--outputGrammar g = case g of
--       Text.Parser.Core.EOF => putStrLn "EOF"
--       --(Text.Parser.Core.Fail s) => putStrLn ("Fail"++s)
--       Text.Parser.Core.Commit => putStrLn "Commit"

-- I had to change Grammar in Text.Parser.Core to make it 'public export'
-- so that this function can see these constructors
-- 
outputGrammar2 : Nat -> Grammar tok consume ty -> IO ()
outputGrammar2 Z g = putStrLn "limit"
outputGrammar2 (S n) (Text.Parser.Core.Empty ty) = putStrLn "Empty"
outputGrammar2 (S n) (Text.Parser.Core.Terminal tok) = putStrLn "Terminal"
outputGrammar2 (S n) (Text.Parser.Core.NextIs tok) = putStrLn "NextIs"
outputGrammar2 (S n) Text.Parser.Core.EOF = putStrLn "EOF"
outputGrammar2 (S n) (Text.Parser.Core.Fail s) = putStrLn ("Fail"++s)
outputGrammar2 (S n) Text.Parser.Core.Commit = putStrLn "Commit"
outputGrammar2 (S n) (Text.Parser.Core.SeqEat g1 g2) = do putStrLn "SeqEat"
                                                          (outputGrammar2 n g1)
                                                          putStrLn " | "
                                                          --(outputGrammar2 n g2)
outputGrammar2 (S n) (Text.Parser.Core.SeqEmpty g1 ag2)  = putStrLn "SeqEmpty"
outputGrammar2 (S n) (Text.Parser.Core.Alt g1 g2) = do putStrLn "Alt:"
                                                       (outputGrammar2 n g1)
                                                       -- above causes:
                                                       -- Codegen error in Idris.Parser.{simpleExpr_2}
                                                       putStrLn " | "
                                                       --(outputGrammar2 n g2)
outputGrammar2 (S n) g = putStrLn "invalid"


outputGrammar : Grammar tok consume ty -> IO ()
outputGrammar g = outputGrammar2 5 g

