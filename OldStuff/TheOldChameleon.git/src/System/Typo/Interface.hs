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
-- The Typo GUI interface.
--
--------------------------------------------------------------------------------

module System.Typo.Interface (
    interface
) where

import Data.IORef

import Foreign.C
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc
import Graphics.UI.WX
import Graphics.UI.WXCore

import Config.Global
import System.Typo.Core

--------------------------------------------------------------------------------

-- start the interface
interface :: State -> IO ()
interface st = start (iface st)

iface :: State -> IO ()
iface st = do 
    f <- frame [text := "Typo!"]
    writeIORef (outerFrame st) f

    s <- splitterWindow f [style := wxSP_3D]

    -- source text window
    stxt <- textCtrl s [font := fontFixed { _fontSize = 12 },
			outerSize := sz 400 200]
    textCtrlSetEditable stxt False
    writeIORef (srcTextCtrl st) stxt

    -- diag. text window
    diag <- singleListBox s [-- font := fontFixed { _fontSize = 12 },
			     on select := diagSelect st]
    writeIORef (diagListBox st) diag
    
    -- menu items
    file    <- menuPane [text := "&File"]
    mOpen   <- menuItem file [text := "&Open",
			      help := "Open a source file",
			      on command := selectFile st f]
    mReload <- menuItem file [text := "&Reload",
			      help := "Reload the current source file",
			      on command := reloadFile st ]
    mQuit   <- menuItem file [text := "&Quit", 
			      help := "Exit the program",
			      on command := close f]
    set f [menuBar := [file]]
    
    
    -- status bar
    stat <- statusField [text := "Welcome"]
    set f [statusBar := [stat]]
    writeIORef (status st) stat

    -- set the layout
    set f [layout := margin 5 $ fill $ 
		     hsplit s 5 200 (widget stxt) (widget diag),
	   clientSize := sz 600 300]
 
    -- Do a `reload' to process the current file (which may have been specified
    -- as a commandline argument.)
    reloadFile st

  where
   
    -- annoyingly, textCtrlPositionToXY places its result directly in memory
    reportRowCol c t = do
	let bs = sizeOf (1::CLong)
	pr <- mallocBytes bs
	pc <- mallocBytes bs
	ps <- mallocBytes bs
	pe <- mallocBytes bs
	-- get the start and end positions of the current selection
	textCtrlGetSelection t ps pe
	s <- peek (ps :: Ptr CInt)
	e <- peek (pe :: Ptr CInt)
	-- get the row and column of the start of the selection
	textCtrlPositionToXY t (fromIntegral s) pc pr
	sr <- peek (pr :: Ptr CInt)
	sc <- peek (pc :: Ptr CInt)

	-- get the row and column of the end of the selection
	textCtrlPositionToXY t (fromIntegral e) pc pr
	er <- peek (pr :: Ptr CInt)
	ec <- peek (pc :: Ptr CInt)

	c (fromIntegral s) (fromIntegral e)
	putStrLn ("s: " ++ show s ++ "  e: " ++ show e)
	putStrLn (show (sr,sc) ++ " - " ++ show (er,ec))
	
   
    blab t = do
	str <- textCtrlGetStringSelection t
	putStrLn str


-- Pulls up a file selection dialogue and stores the name of the selected file 
-- in the state.
-- It should also call the appropriate Core function, to kick off the
-- Chameleon pipeline.
selectFile :: State -> Frame a -> IO ()
selectFile st@(State { filename = ref_fn, options = ref_opts }) f = do
    fn <- readIORef ref_fn
    putStrLn ("current file: " ++ fn)
    let wild = [("Any File", ["*"]), 
		("Haskell Files (*.hs)", ["*.hs"]), 
		("Chameleon Files (*.ch)", ["*.ch"])]
	header = "Select a Source File"
    mfn <- fileOpenDialog f True True header wild "" defaultFilename
    case mfn of
	-- no file selected
	Nothing  -> return ()

	Just fn' -> do
	    putStrLn ("selected file: " ++ show fn')
	    writeIORef ref_fn fn'
	    opts <- readIORef ref_opts
	    writeIORef ref_opts (opts { inputFiles = [fn'] })
	    processCurrentFile st

-- Reloads the current file, passing it through the Chameleon pipeline again.
reloadFile :: State -> IO ()
reloadFile st = processCurrentFile st





--------------------------------------------------------------------------------
-- MISC.

{-
    -- do some colouring
    let red = rgb 255 0 0 
    attr <- textAttrCreateDefault
    textAttrSetBackgroundColour attr red
    let colour s e = textCtrlSetStyle stxt s e attr
    set stxt [on clickRight := const (reportRowCol colour stxt)]
    textCtrlSetEditable stxt False
    set stxt [text := "Your program text here! ($5)"]
-}
