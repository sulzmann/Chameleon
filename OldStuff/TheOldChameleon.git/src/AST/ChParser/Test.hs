module Main where

import Monad
import System
import IO

import AST.ChParser.Parser
import AST.Desugarer
import Misc
import Config.Global
import Misc.Result
import AST.External as E
import AST.Internal as I
-- import AST.RETrans
--import System.Control

main = do
    as <- getArgs
    case as of
	[]    -> putStrLn "no filename specified!" >> exitFailure
	(f:_) -> do h <- openFile f ReadMode
		    str <- hGetContents h
		    let eres = parseProg f 0 str
		    putStrLn "\n *** EXTERNAL AST *** "
		    print eres
		    case eres of
			      Failure es b -> exitFailure 
			      -- don't care, it should be (causeFailure es ... )
			      Success es (_rest, scs, n, ast, toks) ->
				  ( do
				    let e@(E.Prog ((E.Module _ _ _ edecs _):_)) = ast
				    let ped = pretty edecs
				    putStrLn ped
                                    putStrLn "\n *** INTERNAL AST *** \n"
                                    let (iast,_) = desugarProg opts ast
                                    print iast
                                    putStrLn (pretty iast)
				  )
	where opts = Options { colourText  = True,
			       verbosity   = VerbLevel 0,
			       inputFiles  = [],
			       outputFile  = defaultOutputFilename,
			       modulePaths = [".", ""],
			       backend	   = defaultBackEnd,
			       importImplicit = True,
			       checkKinds  = True,
                               checkIntSyntax = False,
                               xhaskellExt = True,
			       lastStage      = AllDone, 
			       mimicGHC = False 
                             }

