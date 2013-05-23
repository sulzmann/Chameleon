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
-- The global Chameleon system state. 
-- Contains configuration data, the current program, and inferred information.
-- Also has the top-level system monad definition.
--
--------------------------------------------------------------------------------

module System.Control 
where

import IO
import List
import Monad
import Maybe

import qualified AST.External as Ext
import AST.SrcCommand
import AST.Token
import AST.Internal
import AST.Exports
import AST.SrcInfo
import AST.CallGraph

import Core.CHR
import Core.InfGoal
import Core.InfResult
import Core.Justify

import Config.Global
import System.Modules

import Misc
import Misc.Print
import Misc.Error
import Misc.Result
import Misc.Pretty

--------------------------------------------------------------------------------

-- TODO: - add a table of module data to the state
--	 - at any time we're processing only one module, so all other global
--	   information refers to that one active module only. (NOTE: this
--	   active module may not directly correspond to a single real module, 
--	   i.e. it may actually be a combination of a set of mutually dependent 
--	   modules into one large pseudo-module.)

data State = State { -- all configuration options
		     config :: Options,

		     -- batches left to process
		     batches :: [Batch],

		     -- all batches
		     allBatches :: [Batch],

		     -- information about all the modules processed so far
		     -- NOTE, IMPORTANT: The module info will be stored in
		     -- reverse dependency order. That's because as the modules
		     -- are processed in dependency order, we place their info.
		     -- on the front of this list.
		     modules :: [ModuleInfo],


-- The following stuff applies to the active module only!

		     -- the source filename
		     srcFilename :: FilePath,

		     -- the source program text
		     srcProg :: String,

		     -- source tokens
		     srcTokens :: TokenStream,

		     -- source commands (commands/options embedded in the src)
		     srcCommands :: [SrcCommand],
	
		     -- the program in external AST format
		     extProg :: Ext.Prog,

		     -- the program in internal AST format
		     intProg :: Prog,

		     -- all of the SrcInfo labels from the external AST
		     srcInfos :: SrcInfoTable,

		     -- all let-bound variables in the program
		     letIds  :: [Id],

		     -- the call graph
		     callGraph :: CallGraph,

		     -- a normalised call graph
		     normCallGraph :: NormCallGraph,

		     -- strongly connected components, topologically sorted
		     sccs :: [SCC],

		     -- just the let-bound variables which are recursive
		     recursiveIds :: [Id],
	
		     -- original CHR rules
		     originalCHRs :: [CHR],

		     -- reduced/simplified CHR rules
		     reducedCHRs :: [CHR],

		     -- inference goals
		     infGoals :: [InfGoal],

		     -- inference results
		     infResults :: [InfResult],
	
		     -- loc. info, classify program locations by `type'
		     locInfo :: LocInfo,
	
		     -- ucons matches (for evidence construction)
		     uconsMatches :: Matches,

		     -- fresh number store
		     uniqueInt :: Int }


-- initial, empty state 
emptyState :: State
emptyState = State (un "config") (un "batches") (un "allBatches") 
		   (un "modules") 
		   (un "srcFilename") (un "srcProg") (un "srcTokens")
		   (un "srcCommands") (un "extProg") (un "intProg") 
		   (un "srcInfos")
		   (un "letIds") (un "callGraph") 
		   (un "normCallGraph") (un "sccs") (un "recursiveIds") 
		   (un "originalCHRs") (un "reducedCHRs") 
		   (un "infGoals") (un "infResults") 
		   (un "locinfo") (un "uconsMatches")
		   (un "uniqueInt")
  where
    un str = bug ("uninitialised `" ++ str ++ "' in Sys state")


-- state component modifiers
config' :: (Options -> Options) -> State -> State
config'  f st	    = st {config  = f (config  st)}
batches' f st	    = st {batches = f (batches st)}
allBatches' f st    = st {allBatches = f (allBatches st)}
modules' f st	    = st {modules = f (modules st)}

srcFilename' f st   = st {srcFilename = f (srcFilename st)}
srcProg' f st	    = st {srcProg = f (srcProg st)}
srcTokens' f st	    = st {srcTokens = f (srcTokens st)}
srcCommands' f st   = st {srcCommands = f (srcCommands st)}
extProg' f st	    = st {extProg = f (extProg st)}
intProg' f st	    = st {intProg = f (intProg st)}
srcInfos' f st	    = st {srcInfos = f (srcInfos st)}
letIds'  f st	    = st {letIds  = f (letIds  st)}
callGraph' f st	    = st {callGraph = f (callGraph st)}
normCallGraph' f st = st {normCallGraph = f (normCallGraph st)}
sccs' f st	    = st {sccs = f (sccs st)}
recursiveIds' f st  = st {recursiveIds = f (recursiveIds st)}
originalCHRs' f st  = st {originalCHRs = f (originalCHRs st)}
reducedCHRs'  f st  = st {reducedCHRs = f (reducedCHRs st)}
infGoals' f st	    = st {infGoals = f (infGoals st)}
infResults' f st    = st {infResults = f (infResults st)}
locInfo' f st	    = st {locInfo = f (locInfo st)}
uconsMatches' f st  = st {uconsMatches = f (uconsMatches st)}
uniqueInt' f st	    = st {uniqueInt = f (uniqueInt st)}

----------------------------------------

currentModuleName :: Sys IdStr
currentModuleName = do 
    ext_ast <- stGet extProg
    case ext_ast of
	Ext.Prog [] -> bug "no module in this program!"
	Ext.Prog ((Ext.Module id _ _ _ _):_) -> return (idStr id)
--        Ext.Prog ((Ext.Xmodule id _ _ _):_) -> return (idStr id)

----------------------------------------

-- Information we've inferred about a particular module, includes:
--  o Name of the module
--  o Type of the module 
--    * Haskell module, or
--    * XHaskell module
--  o The name of the file containing it
--  o Things exported
--  o Things imported
--  o Other modules it imports
--  o The inference result for the module
data ModuleInfo = ModuleInfo { moduleId :: IdStr,
                               moduleType :: ModType,
			       moduleFilename :: String,
			       moduleExports :: [Exported],
			       moduleImports :: [Imported],
			       modulesImported :: [IdStr],
			       moduleInfResults :: [InfResult] }
    deriving (Show)


instance Pretty ModuleInfo where
   pretty (ModuleInfo id mt name exps imps modImp inf) =
      "ModuleId: " ++ id ++ "\n" ++
      "ModuleType: "++ (show mt) ++ "\n" ++
      "FileName: " ++ name ++ "\n" ++
      "Exports: " ++ (show exps) ++ "\n" ++
      "Imports: " ++ (show imps) ++ "\n" ++
      "Modules Imported: " ++ (show modImp) ++ "\n" ++
      "Inf Results: " ++ (pretty inf) ++ "\n"

blankModuleInfo :: ModuleInfo
blankModuleInfo = ModuleInfo "" Cmod "" [] [] [] []

moduleId' f m	      = m { moduleId = f (moduleId m) }
moduleType' f m       = m { moduleType = f (moduleType m) }
moduleFilename' f m   = m { moduleFilename = f (moduleFilename m) }
moduleExports' f m    = m { moduleExports = f (moduleExports m) }
moduleImports' f m    = m { moduleImports = f (moduleImports m) }
modulesImported' f m  = m { modulesImported = f (modulesImported m) }
moduleInfResults' f m = m { moduleInfResults = f (moduleInfResults m) }

getModuleInfoById :: IdStr -> Sys (Maybe ModuleInfo)
getModuleInfoById id = 
    Sys (\st -> return2 (st, let ms = filter ((id==) . moduleId) (modules st)
			     in  listToMaybe ms))

updateModuleInfoById :: IdStr -> (ModuleInfo -> ModuleInfo) -> Sys ()
updateModuleInfoById idstr f = 
    Sys (\st -> let (ms,other) = partition ((idstr==) . moduleId) (modules st)
		    mm  = listToMaybe ms
		    mi  = maybe (blankModuleInfo { moduleId = idstr }) id mm
		    st' = st { modules = f mi : other }
		in  return2 (st', ()))
		
-- replaces the info entry with the same id (or adds it if its not there)
replaceModuleInfo :: ModuleInfo -> Sys () 
replaceModuleInfo m@(ModuleInfo {moduleId = id}) = do
    ms <- stGet modules
    let ms' = m : filter ((id/=) . moduleId) ms
    stSet modules' ms'

----------------------------------------

-- A result where the error may contain a copy of the last state.
type SysResult b = Result State b

-- the primary system monad, which contains the system state
newtype Sys a = Sys (State -> IO (SysResult (State, a)))

instance Monad Sys where

    -- return :: a -> Sys a
    return a = Sys (\st -> return (mkSuccess (st, a)))

    -- (>>=) :: Sys a -> (a -> Sys b) -> Sys b
    (Sys a) >>= f = Sys (\s -> do r <- a s 
				  case r of
				    Failure e s -> return (Failure e s)
				    Success e (s',a') -> do
					let Sys f' = f a' 
					r' <- f' s'
					return (r >> r'))

    -- fail :: String -> b
    fail str = bug ("somebody called the Sys monad's fail method: `"++str++"'")

----------------------------------------

-- run a Sys command with the given state, returning just the result
runSys :: State -> Sys a -> IO (SysResult a)
runSys st (Sys c) = do
    res <- c st
    return $ case res of
	Failure e s	 -> Failure e s
	Success e (st,a) -> Success e a

-- run a Sys command with the given state, returning the result and final state
runSysAll :: State -> Sys a -> IO (SysResult (State, a))
runSysAll st (Sys c) = c st

-- perform an IO action
doIO :: IO a -> Sys a
doIO io = Sys (\st -> do r <- io
			 return2 (st, r))

-- accumulating error messages
addError :: HasSrcInfo a => a -> Msg -> Sys ()
addError x m =
    let err = mkError (getSrcInfo x) m
    in Sys (\st -> return (Success [err] (st, ())))

instance AccumError Sys where
    addErrorMsg = addError

-- Causes a failure, saving the current state inside the Failure result.
causeFailure :: [Error] -> Sys ()
causeFailure e = Sys (\st -> return (Failure e st))

----------------------------------------

-- functions for examining and updating the state inside the Sys monad

stGet :: (State -> a) -> Sys a
stGet f = Sys (\st -> return2 (st,f st))

stUpdate :: (State -> State) -> Sys ()
stUpdate f = Sys (\st -> return2 (f st,()))

-- replaces a state field
stSet :: ((a -> a) -> State -> State) -> a -> Sys () 
stSet f x = stUpdate (f (const x))

getState :: Sys State
getState = Sys (\st -> return (mkSuccess (st, st)))

----------------------------------------

newInt :: Sys Int
newInt = do n <- stGet uniqueInt
	    incUniqueInt
	    return n
  where
    incUniqueInt = stUpdate (uniqueInt' (+1))

----------------------------------------

puts, putsLn :: String -> Sys ()
puts   = doIO . putStr
putsLn = doIO . putStrLn

hPuts, hPutsLn :: Handle -> String -> Sys ()
hPuts   h = doIO . hPutStr h
hPutsLn h = doIO . hPutStrLn h 

----------------------------------------

getConfig :: (Options -> a) -> Sys a
getConfig f = Sys (\st -> return2 (st, f (config st)))

-- prints the string if we're at or above the given verbosity level
verb :: Int -> [String] -> Sys ()
verb n strs = do
    v <- getConfig verbosity
    let left = replicate n '>'
	str  = unlines (map (left++) strs)
    when (v >= VerbLevel n) (doIO (putStr str))

verb1 msg = verb 1 [msg]

-- True if the current verbosity level is at or above the given int
asVerboseAs :: Int -> Sys Bool
asVerboseAs n = do
    v <- getConfig verbosity
    return (v >= VerbLevel n)

----------------------------------------

-- Grabs all the source text-related data and wraps it up for the text printer.
getSrcTextData :: Sys SrcTextData
getSrcTextData = do 
    src <- stGet srcProg
    sit <- stGet srcInfos
    ts  <- stGet srcTokens
    return (mkSrcTextData src sit ts)

----------------------------------------

instance HasNumSupply Sys where
    freshInt = newInt

--------------------------------------------------------------------------------

-- initialises state with configuration options
initialiseState :: Options -> State
initialiseState opts = emptyState { config = opts, 
				    uniqueInt = 1 }


--------------------------------------------------------------------------------

checkE :: E a -> Sys ()
checkE e = case e of
    Err msg -> let err = mkSuperFatalError msg
	       in  causeFailure [err]

    Succ x  -> return ()

--------------------------------------------------------------------------------

allDone :: Sys ()
allDone = verb1 "All done"
