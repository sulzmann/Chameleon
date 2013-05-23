--------------------------------------------------------------------------------
--
-- Copyright (C) 2005 The Chameleon Team
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
-- The Typo Core
--
-- The core establishes all of the state, as well as interfacing with the rest 
-- of the Chameleon system (which provides all of the parsing, inference and 
-- constraint reasoning functionality.)
-- 
--------------------------------------------------------------------------------

module System.Typo.Core (
    State(..), initialState, 
    defaultFilename,
    
    processCurrentFile, diagSelect
) where

import Data.IORef
import Graphics.UI.WX
import Graphics.UI.WXCore

import Misc
import Misc.Error
import Misc.Result
import AST.SrcInfo

import Config.Global
import qualified System.Control as Ch
import System.Batch	      (batchModules)
import System.Pipeline hiding (processBatches, processModule, processCycle)
import System.Control  hiding (State)
import System.Modules

import Foreign.C
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc

--------------------------------------------------------------------------------

type StateRef = IORef State

-- Typo state, contains:
-- - the name of the current file
data State = State { filename :: IORef String,
		     options  :: IORef Options,
		     chState  :: IORef Ch.State,
		     errors   :: IORef [Error],
		     outerFrame  :: IORef (Frame ()),
		     srcTextCtrl :: IORef (TextCtrl ()),
		     diagListBox :: IORef (SingleListBox ()),
		     status :: IORef StatusField }

-- The filename may already be part of the options.
initialState :: Options -> IO State
initialState opts = do
    fn <- newIORef (let fs = inputFiles opts 
		    in  if null fs then "" else head fs)
    opts' <- newIORef opts
    cst   <- newIORef (initialiseState opts)
    errs  <- newIORef []
    ofrm  <- newIORef (un "outerFrame")
    stxt  <- newIORef (un "srcTextCtrl")
    dtxt  <- newIORef (un "diagListCtrl")
    stat  <- newIORef (un "status")  
    return (State fn opts' cst errs ofrm stxt dtxt stat)
  where
    un f = bug ("uninitialised State field " ++ f)

defaultFilename :: String
defaultFilename = ""

--------------------------------------------------------------------------------

clearInterface :: State -> IO ()
clearInterface (State {srcTextCtrl = ref_stxt, diagListBox = ref_diag}) = do
    stxt <- readIORef ref_stxt
    diag <- readIORef ref_diag
    set stxt [text := ""]
    itemsDelete diag

--------------------------------------------------------------------------------

-- Runs the current file (as named in the state), through the Chameleon
-- pipeline process all the way to type checking. (This includes *all* the
-- preceding steps, like processing imported modules.)
processCurrentFile :: State -> IO ()
processCurrentFile st@(State ref_fn ref_opts ref_cst ref_errs _ ref_stxt _ _) = do
    fn <- readIORef ref_fn
    if fn == defaultFilename 
      then return ()
      else do
	-- reinitialise the Chameleon state, and process the current file
	putStrLn ("processing file " ++ fn)
	clearInterface st
	opts <- readIORef ref_opts
	let cst  = initialiseState opts
	    proc = batchModules >> processBatches st
	res <- runSysAll cst proc
	case res of
	  Success e (cst',_) -> do let src = srcProg cst'
				   stxt <- readIORef ref_stxt
				   setSrcTextControl st src
				   writeIORef ref_cst cst'
				   writeIORef ref_errs e
				   reportErrors e

	  Failure e cst' 
	    -- If the error is SuperFatal, then we couldn't even load the source
	    | any (isSuperFatal.errorSeverity) e -> do writeIORef ref_errs e
						       reportErrors e

	    -- do we keep the old Chameleon state or what?
	    | otherwise -> do let src = srcProg cst'
			      stxt <- readIORef ref_stxt
			      setSrcTextControl st src
			      writeIORef ref_errs e
			      reportErrors e

  where
    reportErrors = reportErrorsDiag st

-- puts error messages (diagnoses) in a list box 
reportErrorsDiag :: State -> [Error] -> IO ()
reportErrorsDiag (State { diagListBox = ref_diag }) es = do
    diag <- readIORef ref_diag
    let msgs = errorsToStrings es
    mapM_ (itemAppend diag) msgs

-- a diagnosis (error message) has been selected
-- jump to the corresponding source location
diagSelect :: State -> IO ()
diagSelect st@(State { diagListBox = ref_diag, errors = ref_errs }) = do
    diag <- readIORef ref_diag
    errs <- readIORef ref_errs
    n <- listBoxGetSelection diag
    -- putStrLn ("selected: " ++ show n)
    let Error sev info msg = errs !! n
	r = srcRow info
	c = srcCol info
    placeSrcCursor st r c

-- place the source text cursor at the given row, column location, selecting
-- the text there
placeSrcCursor :: State -> Int -> Int -> IO ()
placeSrcCursor st@(State { srcTextCtrl = ref_stxt }) r c = do
    stxt <- readIORef ref_stxt
    pos  <- textCtrlXYToPosition stxt (point c0 r0)
    textCtrlSetInsertionPoint stxt pos
    textCtrlSetSelection stxt pos (pos+1)
    -- repaint stxt
    -- repaintFrame st
  where
    r0 = r - 1
    c0 = c - 1


-- puts the given string in the source text control
-- also sets the `insertion point' to the top of the text
setSrcTextControl :: State -> String -> IO ()
setSrcTextControl (State { srcTextCtrl = ref_stxt }) str = do
    stxt <- readIORef ref_stxt
    set stxt [text := str]
    textCtrlSetInsertionPoint stxt 0
    -- repaint stxt


-- Places some text into the status bar.
writeStatusField :: State -> String -> IO ()
writeStatusField (State { status = ref_sb }) str = do
    sb <- readIORef ref_sb
    set sb [text := str]

writeStatusFieldSys :: State -> String -> Sys ()
writeStatusFieldSys st = doIO . writeStatusField st

repaintFrame :: State -> IO ()
repaintFrame (State { outerFrame = ref_frm }) = do 
    frm <- readIORef ref_frm
    repaint frm

--------------------------------------------------------------------------------

-- Basically a copy of the very top of the Chameleon pipeline, but with GUI
-- actions interspersed between pipeline stages.
processBatches :: State -> Sys ()
processBatches st = do
    writeStatusFieldSys st ("Processing module batches")
    stSet modules' []
    bs <- stGet batches
    proc bs
  where
    proc [] = stSet batches' []
    proc bbs@(b:bs) = do
        stSet batches' bbs
        case b of
            [m] -> processModule st m
            ms  -> processCycle st b
        proc bs


-- process a singleton batch
processModule :: State -> ModuleName -> Sys ()
processModule st m = do
    stSet srcFilename' fn
    mapM_ doStage stages
  where
    fn = addChSuffix m

    doStage (stage,msg) = do
	writeStatusFieldSys st msg
	doIO (putStrLn msg)
	doIO (repaintFrame st)
	stage

    stages = [ (return (), "Processing Module in `" ++ fn ++ "'"),
	       (getSourceText m, "Reading source text"),
               (parseSourceText, "Parsing source text"),
               (checkExternalAST, "Checking external AST"),
               (desugarExternalAST, "Desugaring external AST"),
               (analyseInternalAST, "Analysing internal AST"),
               -- (validateKinds, "Validating kinds"),
               (validateTypes, "Validating Types") ]
    

longPause = (mapM_ (doIO . putChar) (replicate 50000 '.'), "long pause ")

----------------------------------------
-- process a cycle of modules
processCycle :: State -> Batch -> Sys ()
processCycle = bug "Support for cyclical modules not implemented yet!"
