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
-- | Defines all source-based type debugger commands.
-- NOTE: None of these commands are currently processed by the implementation
--	 (it ignores them.) In fact, I'm not sure that the parser even accepts
--	 them.
--------------------------------------------------------------------------------

module AST.SrcCommand (
    SrcCommand(..)
) 
where

import AST.SrcInfo
import AST.External

--------------------------------------------------------------------------------
-- source-based debugger commands

-- | The syntax of source-based debugger commands.
data SrcCommand = SCTypeLoc SrcInfo		    -- ^ type command
		| SCTypeVar Id SrcInfo		    
		| SCExplainLoc SrcInfo TSchm	    -- ^ explain command
		| SCExplainVar Id SrcInfo TSchm

instance Show SrcCommand where 
    show (SCTypeLoc l)	      = "SCTypeLoc " ++ show l
    show (SCTypeVar i l)      = "SCTypeVar " ++ show (i, l)
    show (SCExplainLoc l t)   = "SCExplainLoc " ++ show l
    show (SCExplainVar i l t) = "SCExplainVar " ++ show (i, l)

