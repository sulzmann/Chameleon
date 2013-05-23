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
-- Responsible for finding all module batches.
--
-- NOTE: This was factored out of System.Modules to prevent a cycle.
--  
--------------------------------------------------------------------------------

module System.Batch (
    batchModules
) 
where

import Monad

import Misc
import Misc.Error
import Misc.Result
import Misc.ErrorMsg
import Config.Global
import System.Control
import System.Modules

--------------------------------------------------------------------------------

-- Organise modules into dependency-directed batches.
-- Also record the imports for each module.
-- NOTE: This is the first time that we attempt to load any source file; which
--	 may fail. It also fails if no input file is specified.
batchModules :: Sys ()
batchModules = do
    fs <- getConfig inputFiles
    case fs of
        []  -> let msg = errorMsgNoSrc ["no source file specified"]
		   err = mkSuperFatalError msg
	       in  causeFailure [err]

        (f:fs) -> do
            when (not (null fs))
                 (putsLn (warningMsgNoSrc
                            ["only reading the first file (`" ++ f ++ "')"]))
            proc f
  where
    proc :: String -> Sys ()
    proc fn0 = do
        verb1 "Calculating module dependencies"
	ps  <- getConfig modulePaths
	imp <- getConfig importImplicit
        let fn = dropSuffix fn0
        res <- doIO (moduleBatches imp ps fn)
	case res of
	  Failure es _  -> causeFailure es
	  Success es bs -> do
	    verb 2 [arrows (map show bs)]
	    stSet allBatches' bs
	    stSet batches' bs

