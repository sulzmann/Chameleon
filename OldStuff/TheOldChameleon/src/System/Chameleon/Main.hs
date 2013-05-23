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
-- Chameleon! (the compiler)
--
--------------------------------------------------------------------------------

module Main (
    main
) where

import System

import Misc
import Misc.Error
import Misc.Result
import System.Batch	    (batchModules)
import System.Pipeline	    (processBatches)
import System.Link	    (linkObjects)
import System.Control	    
import Config.CmdLine	    (parseCmdLineArgs)
import Config.Global

--------------------------------------------------------------------------------

-- Reads and parses command-line options. 
-- Then generates an initial state and runs the Chameleon compiler.
main :: IO ()
main = do
    as <- getArgs
    let fs    = parseCmdLineArgs as
	opts  = flagsToOptions fs
        state = initialiseState opts
	chameleon = batchModules >>
		    processBatches >>
		    linkObjects >>
		    allDone
    res <- runSys state chameleon
    let errs = resultErrors res
    reportErrors errs
    if isSuccess res
      then exitSuccess
      else exitFailure
