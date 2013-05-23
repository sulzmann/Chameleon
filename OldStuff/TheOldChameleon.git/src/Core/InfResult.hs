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
-- Defines inference results. These are the result of running some inference
-- goal. They contain enough information to process the result (e.g. evidence
-- construction, error reporting) whether inference succeeded or failed.
--
-------------------------------------------------------------------------------

module Core.InfResult (
    InfResult(..), formatInfResult, isInfFailure, isInfSuccess, isFailure
)
where

import Misc
import AST.Internal (Id, idStr)
import Core.Constraint
import Core.Types

--------------------------------------------------------------------------------

-- Represents the result of type inference; success or failure.
-- In the successful case, the constraint is likely to be quite minimal
-- (containing type class constraints and equations defining the t,l,v
-- components.) If the result is a failure, the constraint will consist of all
-- constraints which were added to the store while solving.
data InfResult = InfSuccess { resId   :: Id,
			      resTLV  :: [Type],
			      resCons :: Constraint }

		-- resTypes: maps each variable (representing the type at a
		--	     location -- probably the RHS of a let binding) to
		--	     a resulting type.
		-- resCons: all the left-over user constraints (type class)
	       | InfSuccessW { resId :: Id,
			       resType :: Type,
			       resUConses :: [UCons]
                             }

	       | InfFailure { resId   :: Id,
			      resCons :: Constraint }
	       
	       | InfFailureUniv { resId   :: Id,
				  resVar  :: Var,   -- became instantiated
				  resVars :: [Var], -- all other univ. variables
				  resCons :: Constraint }

	       | InfFailureUnivEsc { resId   :: Id,
				     resT    :: Var,	-- var. of top-lvl type
				     resType :: Type, 	-- bad top-level type
				     resOut  :: [Var], 	-- univ. variables
				     resCons :: Constraint }

	       | InfFailureUConsUnmatched { resId :: Id,
					    resUCons :: UCons }
				  
	       | SubSuccess { resId :: Id }
    deriving (Show)

-- FIXME: use these to extract result out of any kind of success value, W or not
-- resT :: InfResult -> Type
-- resConstraint :: InfResult -> Constraint

isInfSuccess, isSubSuccess, isInfFailure, isFailure :: InfResult -> Bool
isInfSuccess (InfSuccess {}) = True
isInfSuccess (InfSuccessW {}) = True
isInfSuccess (SubSuccess {}) = True
isInfSuccess _ = False

isSubSuccess (SubSuccess {}) = True
isSubSuccess _ = False

isInfFailure (InfFailure {}) = True
isInfFailure _ = False

isFailure = not . isInfSuccess


instance Pretty InfResult where
    pretty = formatInfResult

--------------------------------------------------------------------------------

formatInfResult :: InfResult -> String
formatInfResult r = case r of
    
    InfFailure id c -> name ++ " :: FAILED " 

    InfFailureUniv id v vs c -> name ++ " :: FAILED, universal var. " ++ 
				pretty v ++ " instantiated"

    InfFailureUnivEsc id _ v o _ -> name ++ " :: FAILED, universal var. " ++ 
				    pretty v ++ " escaped via " ++ pretty o

    InfFailureUConsUnmatched id uc -> name ++ " :: FAILED, unmatched ucons: " ++
				      pretty uc

    SubSuccess id -> name ++ " TYPE OK"

    InfSuccess id [] c -> name ++ " :: SUCCESS" 

    InfSuccessW id t ucs -> 
	    let (t',ucs') = prettyRename (t,ucs)
		ucs_str | null ucs' = ""
			| singleton ucs' = pretty ucs' ++ " => " 
			| otherwise = "(" ++ pretty ucs' ++ ") => "
	    in  name ++ " :: " ++ ucs_str ++ pretty t'

    InfSuccess id tlv c ->
	    let typ = head tlv
		ucs = cUCons c
		(typ',ucs') = prettyRename (typ,ucs)
		ucs_str | null ucs' = ""
			| singleton ucs' = pretty ucs' ++ " => " 
			| otherwise = "(" ++ pretty ucs' ++ ") => "
		typ_str = pretty typ'
	    in  name ++ " :: " ++ ucs_str ++ typ_str

  where
    name = infixParens (idStr (resId r))
