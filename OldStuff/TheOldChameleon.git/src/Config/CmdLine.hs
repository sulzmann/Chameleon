--------------------------------------------------------------------------------
--
-- Copyright (C) 2004 The Chameleon Team
--
-- This program is free software; you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by the Free 
-- Software Foundation; either version 2 of the License, or (at your option) 
-- any later version. This program is distributed in the hope that it will be 
-- useful, but WITHOUT ANY WARRANTY; without even the implied warranty of 
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. 
-- See the GNU General Public License for more details. 
-- You should have received a copy of the GNU General Public License along
-- with this program; if not, write to the Free Software Foundation, Inc., 
-- 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
--
--------------------------------------------------------------------------------
--
-- Parser for command line options.
--
-- Warning: Remember to update multipleEnds when adding new `--just-' flags.
--
-- NOTE: It is okay for us to simply bail out in the event of a command line 
-- parse error. (There can be no sub-system to catch such an error anyway,
-- since nothing can be started.) So, the use of `exit' to print error messages
-- below is acceptable.
--
--------------------------------------------------------------------------------

module Config.CmdLine (
    parseCmdLineArgs
)
where

import Char
import List
import System.Console.GetOpt

import Config.Flags
import Misc
import Misc.Pretty
import Misc.Version
import Misc.ErrorMsg


--------------------------------------------------------------------------------

parseCmdLineArgs :: [String] -> [Flag]
parseCmdLineArgs cl = case getOpt (ReturnInOrder InputFile) options cl of
    (fs,[],[]) -> -- everything parsed
		  handleImmediateFlags (checkConsistency fs)

    (_,_,err)  -> -- parse error(s)
		  let msgs = map (errorMsgNoSrc . (:[])) err ++ [helpMsg]
		  in  exit (newlines msgs)

    _ -> bug "unforseen case in Config.CmdLine.parseCmdLine"

----------------------------------------

-- performs opperations for flags that need to be dealt with immediately
handleImmediateFlags :: [Flag] -> [Flag]
handleImmediateFlags = handleUsage . handleVersion

handleUsage, handleVersion :: [Flag] -> [Flag]
handleUsage   fs = if Usage `elem` fs   then printUsage   else fs
handleVersion fs = if Version `elem` fs then printVersion else fs

printVersion, printUsage :: a
printVersion = exitOkay versionStr
printUsage   = exitOkay (usageInfo usageHeader options)
    where   usageHeader = "Usage:\n\tchameleon [options] <file>\n"

helpMsg = "try `--help' for basic usage information"

----------------------------------------

-- checks that the combination of flags makes sense
checkConsistency :: [Flag] -> [Flag]
checkConsistency = multipleEnds . multipleOutputs 
 
multipleOutputs :: [Flag] -> [Flag]
multipleOutputs fs = 
    let outs = filter (not.null) 
		[ s | f <- fs, let s = case f of OutputFile n -> n
						 StdOut -> "stdout"
						 _ -> "" ]
    in  if length outs > 1 
	then exit (errorMsgNoSrc ["multiple output targets: " ++ 
				  commasAnd (quotes outs) ])
	else fs

-- WARNING: update es as more of these flags are added
multipleEnds :: [Flag] -> [Flag]
multipleEnds fs = 
    let es  = [JustDesugar, JustInferTypes]
	fs' = nub $ filter (`elem`es) fs
    in  if length fs' > 1 
	then exit (errorMsgNoSrc ["multiple final phases: " ++ 
				  commasAnd (showFlags fs')])
	else fs
	

--------------------------------------------------------------------------------

options :: [OptDescr Flag]
options = 
    [ Option ['o'] []	      (ReqArg OutputFile "file")
			       "output file",
 
--    Option []    ["stdout"] (NoArg StdOut)
--			       "write output to stdout",
    
--    Option []    ["just-desugar"] (NoArg JustDesugar)
--			       "output desugared program, then stop",

      Option []    ["just-infer-types"] (NoArg JustInferTypes)
			       "output the inference result, then stop",
 
      Option []	   ["dont-import-implicit"] (NoArg (ImportImplicit False))
			       "don't import implicit modules",

      Option []	   ["dont-check-kinds"] (NoArg (CheckKinds False))
			       "don't validate kinds",

      Option []    ["dont-check-int-syntax"] (NoArg (CheckIntSyntax False))
                               "don't execute internal syntax checks",

      Option []    ["xhaskell"] (NoArg XHaskellExt)
                               "turn on xhaskell extension",

      Option []	   ["clp-type-inference"] (NoArg CLPTypeInference)
			       "use clp-style type inference scheme",
 
      Option []	   ["backend"] (ReqArg (BackEnd . checkBackEnd) "back")
			       "selects a back-end",
    
      Option []    ["no-colour"] (NoArg NoColour)
			       "turn off coloured output",
 
      Option []	   ["verbose"] (OptArg (Verbose . parseVerbose) "level")
			       "set the verbosity level (0-3)",
 
      Option ['v'] ["version"] (NoArg Version) 
			       "show release version",
     
      Option ['h'] ["help"]    (NoArg Usage) 
			       "display help (this text)",

      Option []    ["ghc-style-kinds"] (NoArg GHCStyleKinds)
                                "activate GHC kind solver mode"]

----------------------------------------

parseVerbose :: Maybe String -> Int
parseVerbose Nothing = 1	-- default level if flag is specified
parseVerbose (Just str) = 
    case parseInt str of      
	Nothing -> err
	Just n  -> if n < 0 || n >3 
		   then err
		   else n
  where
    err = exit msg
    msg = errorMsgNoSrc ["Verbosity level must be a number between 0 and 3"]

checkBackEnd :: String -> String
checkBackEnd str = 
    let str' = map toLower str
    in  if str' `elem` backends
	  then str'
	  else let msg = errorMsgNoSrc ["Unknown backend `" ++ str ++ "'",
				        "Available backends: " ++ 
					commas backends]
	       in  exit msg
  where
    backends = ["none", "scheme", "scheme-lazy", "lvm"]

parseInt :: String -> Maybe Int
parseInt s = let s1 = dropWhile isSpace s
		 s2 = takeWhile isDigit s1
	     in  if null s2 then Nothing
			    else Just (read s2)
