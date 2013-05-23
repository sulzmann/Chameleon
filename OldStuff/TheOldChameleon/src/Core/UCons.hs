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
-- User constraints.
--
--------------------------------------------------------------------------------

module Core.UCons (
    UCons(..), njUC,
)
where

import Char
import List

import Misc 
import Core.Name
import Core.Types
import Core.Justify


--------------------------------------------------------------------------------
-- User constraints

data UCons = UC { ucName  :: Name,
		  ucTypes :: [Type],
		  ucJust  :: Just }
    deriving (Eq, Show)

instance Justified UCons where
    getJust = getJust . ucJust
    modJust f uc = uc { ucJust = f `modJust` (ucJust uc) }

instance TypeOps UCons where
    apply s (UC n ts j) = UC n (apply s ts) j
    fv (UC n ts j)	= fv ts

njUC :: Name -> [Type] -> UCons
njUC n ts = UC n ts noJust

instance Pretty UCons where
    pretty (UC n ts j) = 
	let str  = pretty n
	    pred = infixParens str

	    t = head ts
	    -- we can avoid printing parentheses around the type in some cases
	    ts' | fun = tuple
		| (singleton ts && 
		  (isTCon t || isTVar t || isList t || isTuple t)) = pretty t
		| otherwise = paren
	    
	    gap | fun = ""
		| otherwise = " "

	    just = "_" ++ pretty j

	-- NOTE: constraint may not have any type arguments 
	--	(e.g. if it's the `True' token used in the evidence translation)
	in  if null ts then pred
		       else pred ++ gap ++ ts' -- ++ just

      where 
	fun = case dropQual (nameStr n) of 
		(c:_) -> isLower c
		_     -> False
      
	tuple = "(" ++ pretty ts ++ ")"
      
	paren = unwords (map print ts) 
	  where
	    print t | isTVar t || isTCon t = pretty t
		    | otherwise = "(" ++ pretty t ++ ")"

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

