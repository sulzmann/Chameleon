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
-- | Defines built-in constraints (equations).
--------------------------------------------------------------------------------

module Core.BCons (
    BCons(..), 
    flipBC, newBCLeft, newBCRight, bcToPair,

    (=:=), (=+=)
)
where

import List

import Misc
import Core.Types
import Core.Justify

--------------------------------------------------------------------------------

-- | Built-in constraints (equations)
data BCons = Eq { eqLeft  :: Type,	-- ^ left-hand side
		  eqRight :: Type,	-- ^ right-hand side
		  eqJust  :: Just	-- ^ justification
	     }
    deriving (Eq, Show)

eq = Eq

infix 8 =+=
infix 8 =:=

-- | Builds a normal, justified equation.
(=+=) :: Justified a => Type -> Type -> (a -> BCons)
t1 =+= t2 = Eq t1 t2 . getJust

-- | Builds an unjustified equation (uses `noJust'.)
(=:=) :: Type -> Type -> BCons
t1 =:= t2 = Eq t1 t2 noJust

-- builds an unjustified Eq
njEq x y = Eq x y noJust

-- | Replaces the type on the left of the equation.
newBCLeft :: BCons -> Type -> BCons
newBCLeft  (Eq  _ t2 j) t1 = Eq t1 t2 j

-- | Replaces the type on the right of the equation.
newBCRight :: BCons -> Type -> BCons
newBCRight (Eq  t1 _ j) t2 = Eq t1 t2 j

flipBC (Eq t1 t2 j) = Eq  t2 t1 j

bcToPair :: BCons -> (Type,Type)
bcToPair (Eq t1 t2 _) = (t1,t2)

-- NOTE: needs to change if we add non-Eq built-ins
instance Justified BCons where
    getJust = getJust . eqJust
    modJust f bc = bc { eqJust = f `modJust` (eqJust bc) }

instance TypeOps BCons where
    apply s (Eq t1 t2 j) = Eq (apply s t1) (apply s t2) j
    fv (Eq t1 t2 j)	 = fv (t1, t2)

instance Pretty BCons where
    pretty (Eq l r j) = (pretty l ++ "=" ++ pretty r) -- ++ "_" ++ pretty j

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

