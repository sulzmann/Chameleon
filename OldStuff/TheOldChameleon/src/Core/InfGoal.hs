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
-- Defines inference goals. These represent the goal to solve in order to
-- infer the type of some let-bound var.
--
-------------------------------------------------------------------------------

module Core.InfGoal (
    InfGoal(InfGoal, SubGoal, infId, infCons), infTop, infTLV,
    isInfGoal, isSubGoal
)
where

import Misc
import AST.Internal (Id, idStr)
import Core.Constraint
import Core.Types

--------------------------------------------------------------------------------

-- Records the goals to solve in order to infer the type of some let-bound 
-- value. The list of types contains the t,l and v type variables, in that
-- order. (NOTE: if the list contains 1 element, it's a `t', if 2 then they're
-- `t' and `l' respectively, if 3 then `t', `l' and `v'.)
-- WARNING: these must only be type variables!
-- Inf. goals are for type inference, SubGoals are for subsumption checks.
data InfGoal = InfGoal { infId   :: Id,
			 infTop' :: Bool,	-- True if it's top-level
			 infTLV  :: [Var],
			 infCons :: Constraint }

	     | SubGoal { infId	 :: Id,
			 infTLV  :: [Var],
			 infCons :: Constraint }
    deriving Show

infTop :: InfGoal -> Bool
infTop (InfGoal {infTop' = b}) = b
infTop (SubGoal {})            = True

{-
infTLV :: InfGoal -> [Var]
infTLV (InfGoal {infTLV' = t}) = t
infTLV (SubGoal {})            = []
-}

isInfGoal :: InfGoal -> Bool
isInfGoal (InfGoal {}) = True
isInfGoal _ = False

isSubGoal :: InfGoal -> Bool
isSubGoal (SubGoal {}) = True
isSubGoal _ = False

instance Pretty InfGoal where
    pretty (InfGoal id _ ts c) = 
	   "InfGoal " ++ idStr id ++ ", tlv: (" ++ pretty ts ++ "), "++ pretty c
    
    pretty (SubGoal id _ c) = "SubGoal " ++ idStr id ++ " " ++ pretty c

