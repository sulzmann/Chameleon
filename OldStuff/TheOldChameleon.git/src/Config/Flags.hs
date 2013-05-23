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
-- Contains all command line flags.
--
--------------------------------------------------------------------------------

module Config.Flags (
    Flag(..), showFlag, showFlags
)
where

import Debug.Trace

--------------------------------------------------------------------------------

data Flag = 
	  -- misc. flags
	    Version		-- print version information
	  | Usage		-- print usage
	  | Verbose !Int	-- verbosity level
	  | NoColour		-- turn off colour output

	  -- input/output flags
	  | InputFile !String	-- an input file
	  | OutputFile !String  -- an output file
	  | StdOut		-- write output to stdout
	
	  -- module import flags
	  | ImportImplicit !Bool    -- import implicit modules
	  | CheckKinds  !Bool	    -- validate/check kinds
          | CheckIntSyntax !Bool    -- Execute internal syntax checks

          | XHaskellExt		    -- XHaskell extension
	
	  -- Selects the `old' inference scheme, where CHRs are used for HM
	  -- inference (as well as type classes.) Newer scheme is W-based.
	  | CLPTypeInference	    
	
	  -- backend flags
	  | BackEnd !String	    -- selects a backend
	  
	  -- pipeline control flags (only run until a certain compiler stage is
	  -- complete, then report the result of that stage.)
	  | JustDesugar		-- only output the desugarred program
	  | JustInferTypes	-- only output the inference results

          -- flags for kind validation options
	    -- Postpone kind defaulting till end of kind validation
          | GHCStyleKinds 

    deriving (Eq, Ord, Show)

----------------------------------------

showFlags = map showFlag

showFlag :: Flag -> String
showFlag JustDesugar    = "--just-desugar"
showFlag JustInferTypes = "--just-infer-types"
showFlag f = let str = show f 
	     in  trace ("showFlag not defined for flag `" ++ str ++ "'") str
