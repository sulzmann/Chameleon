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
-- Implication constraints.
--
--------------------------------------------------------------------------------


module Core.ICons where

import List

import Misc
import Core.Types
import Core.UCons
import Core.BCons
import Core.Justify


--------------------------------------------------------------------------------
-- Implication constraints

-- NOTE: Annoyingly, the RHS of an implication can't be a `Constraint', since
-- that module imports this one, and so we'd cause a cycle.
data ICons = IC { icVars  :: [Var],
		  icLeft  :: ([UCons], [BCons]),
		  icRight :: ([UCons], [BCons], [ICons]),
		  icJust  :: Just }
    deriving (Eq, Show)

-- unjustified implication, no variables
njIC lhs rhs = IC [] lhs rhs noJust

icAllUCons (IC _ (ucs_l,_) (ucs_r,_,_) _) = ucs_l ++ ucs_r
icAllBCons (IC _ (_,bcs_l) (_,bcs_r,_) _) = bcs_l ++ bcs_r

-- NOTE: these apply to the implication alone, not to the sub-constraints
instance Justified ICons where
    getJust = getJust . icJust
    modJust f ic = ic { icJust = f `modJust` (icJust ic) }

-- it's safe to include the exist. vars in the `free vars', since we
-- apply substitutions to them as well
instance TypeOps ICons where
    apply s (IC vs l r j) = IC (apply s vs) (apply s l) (apply s r) j
    fv (IC vs l r j)	  = fv (l, r, vs)

instance Pretty ICons where
    pretty (IC vs l@(lu,lb) r j) = 
	let arr | null vs   = " >-> "
		| otherwise = " >->^{" ++ pretty vs ++ "} " 
	in  "( " ++ prettyC (lu,lb,[]) ++ arr ++ prettyC r ++ " )"
      where
	prettyC :: ([UCons], [BCons], [ICons]) -> String
	prettyC s = case s of
	    ([],[],[])    -> "True"
	    (ucs,bcs,ics) -> 
		let ps0 = [map pretty ucs, map pretty bcs, map pretty ics]
		    ps1 = filter (not . null) ps0
		    ps2 = intersperse ", " (concat ps1)
		in  concat ps2

