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
-- Constraint Handling Rules (CHRs), as represented within the core Chameleon
-- system.
--
--------------------------------------------------------------------------------

module Core.CHR 
where

import List
import Char

import Misc
import Core.Name
import Core.Justify
import Core.Constraint

--------------------------------------------------------------------------------
-- Constraint Handling Rules

data CHR = SimpRule { chrInfo :: CHRInfo,
		      chrHead :: [UCons],
		      chrBody :: Constraint }
	 | PropRule { chrInfo :: CHRInfo,
		      chrHead :: [UCons],
		      chrBody :: Constraint }
    deriving (Eq, Show)

data CHRInfo = HMRule	    -- indicates a rule related to std. H/M inference
	     | ConsRule	    -- a general-purpose (non-H/M) constraint rule
	     | NoCHRInfo
    deriving (Eq, Show)

isHMRule :: CHR -> Bool
isHMRule chr = chrInfo chr == HMRule

instance Pretty CHR where
    pretty (SimpRule _ c d) = pretty c ++ " <=> " ++ pretty (dropC0UCons d)

    pretty (PropRule _ c d) = pretty c ++ " ==> " ++ pretty (dropC0UCons d)

-- for pretty-printing purposes, we can drop the C0Vars constraints.
dropC0UCons :: Constraint -> Constraint
dropC0UCons c@(C { cUCons = ucs }) = c { cUCons = filter (not . isC0) ucs }
  where
    isC0 (UC { ucName = n }) = nameStr n == "C0Vars!"

--------------------------------------------------------------------------------

-- Reorders the list, placing all propagation rules ahead of simplification.
-- The relative ordering of rules is otherwise maintained.
propsFirst :: [CHR] -> [CHR]
propsFirst chrs = 
    let (ss,ps) = split chrs ([],[])
    in  reverse ps ++ reverse ss
  where
    split [] sps = sps
    split (c:cs) (ss,ps) = case c of
	SimpRule {} -> split cs (c:ss,ps)
	PropRule {} -> split cs (ss,c:ps)


addToCHRBody :: CHR -> Constraint -> CHR
addToCHRBody chr c = chr { chrBody = c /\ chrBody chr }

--------------------------------------------------------------------------------

