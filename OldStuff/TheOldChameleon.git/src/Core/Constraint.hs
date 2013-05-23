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
-- Combines all `primitive' constraints into one Constraint structure.
--
--------------------------------------------------------------------------------

module Core.Constraint (
    module Core.Constraint, 
    module Core.UCons, 
    module Core.BCons,
    module Core.ICons )
where

import Misc
import List

import Core.Types
import Core.UCons
import Core.BCons
import Core.ICons
import Core.Justify

--------------------------------------------------------------------------------
-- Constraints

-- A constraint consists of user, built-in (equational), and implication
-- primitive constraints.
data Constraint = C { cUCons :: [UCons],
		      cBCons :: [BCons],
		      cICons :: [ICons] }
    deriving (Eq, Show)

-- we can only (sensibly) modify a Constraint's justifications
instance Justified Constraint where
    modJust f (C us bs is) = C (modJust f us) (modJust f bs) (modJust f is)

instance TypeOps Constraint where
    apply s (C us bs is) = C (apply s us) (apply s bs) (apply s is)
    fv (C us bs is)	 = fv (us,bs,is)


instance Pretty Constraint where
    pretty (C [] [] []) = "True"
    pretty (C us bs is) = let f xs = map pretty xs
			  in  commas (f us ++ f bs ++ f is)

----------------------------------------
-- standard constraints

trueConstraint, falseConstraint :: Constraint
trueConstraint  = C [] [] []
falseConstraint = bug "define a false constraint"


----------------------------------------
-- operations for combining primitives

class Primitive a where
    toConstraint :: a -> Constraint

instance Primitive a => Primitive [a] where
    toConstraint = andList 

instance (Primitive a, Primitive b) => Primitive (a,b) where
    toConstraint (a, b) = toConstraint a /\ toConstraint b

instance (Primitive a, Primitive b, Primitive c) => Primitive (a,b,c) where
    toConstraint (a, b, c) = toConstraint a /\ toConstraint b /\ toConstraint c

instance Primitive UCons where
    toConstraint uc = C [uc] [] []

instance Primitive BCons where
    toConstraint bc = C [] [bc] []

instance Primitive ICons where
    toConstraint ic = C [] [] [ic]

instance Primitive Constraint where
    toConstraint = id

infixr 7 /\

-- conjoins two primitives 
(/\) :: (Primitive a, Primitive b) => a -> b -> Constraint
a /\ b = addConstraint (toConstraint a) (toConstraint b)

andList :: Primitive a => [a] -> Constraint
andList = foldr (/\) trueConstraint

addConstraint :: Constraint -> Constraint -> Constraint
addConstraint (C u1 b1 i1) (C u2 b2 i2) = C (u1++u2) (b1++b2) (i1++i2)

constraintToTuple :: Constraint -> ([UCons],[BCons],[ICons])
constraintToTuple c = (cUCons c, cBCons c, cICons c)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
{-

instance Eq Constraint where
    (==) (C us1 bs1) (C us2 bs2) = us1 == us2 && bs1 == bs2

instance Justifiable Constraint where
    unJust (C us1 bs1) = unJust us1 ++ unJust bs1
    reJust j (C us1 bs1) = C (reJust j us1) (reJust j bs1)


instance PPrint Constraint where
    pprint (C []  [])  = textPD "True"
    pprint (C ucs bcs) = do ducs <- catListWith "," ucs
			    dbcs <- catListWith "," bcs
			    if not (null ucs) && not (null bcs)
			       then return (ducs <> text "," <> dbcs)
			       else return (ducs <> dbcs)
{-
instance PPrint Constraint where
    pprint (C [] [] [])    = textPD "True"
    pprint (C ucs bcs ics) = do 
	    let ducs = proc ucs
		dbcs = proc bcs
		dics = proc ics
		ds   = [ fromJust md | md <-[ducs, dbcs, dics], isJust md ]
		ds'  = intersperse (textPD ",") ds
	    dds <- sequence ds'
	    retsep dds
      where
	proc [] = Nothing
	proc xs = Just (catListWith "," xs)
-}


instance Show Constraint where show c = pprintPlain c

instance TC Constraint where
   apply s (C ucs bcs) = C (apply s ucs) (apply s bcs)
   fv (C ucs bcs) = (fv ucs) ++ (fv bcs)
   occurs v (C ucs bcs) = (occurs v ucs) || (occurs v bcs)
   rename c = do s <- renameSubst (fv c)
                 return (apply s c)
   format (C ucs bcs) = let u = (format ucs)
                            b = (format bcs)
                        in if u == []
                           then b
                           else if b == []
				then u
			        else "("++u++","++b++")"

----------------------------------------

class Cons a where
    toConstraint   :: a -> Constraint
    fromConstraint :: Constraint -> a

----------------------------------------

trueCons, falseCons :: Constraint
trueCons = C [] []
falseCons = C [] [njEq (TyCon trueName) (TyCon falseName)]

-- also true, but distinct from the standard trueCons
trueConsAlt :: Constraint
trueConsAlt = C [] [njEq (TyCon trueName) (TyCon trueName)]

addCons :: Constraint -> Constraint -> Constraint
addCons (C u1 b1) (C u2 b2) = C (u1++u2) (b1++b2)

bToCons :: BCons -> Constraint
bToCons b = C [] [b]

uToCons :: UCons -> Constraint
uToCons u = C [u] []

consToUs :: Constraint -> [UCons]
consToUs (C us _) = us

consToBs :: Constraint -> [BCons]
consToBs (C _ bs) = bs


bsToCons bs = C [] bs
usToCons us = C us []
cToUCons = consToUs
cToBCons = consToBs

instance Cons UCons where
    toConstraint   = uToCons
    fromConstraint = head . consToUs

instance Cons BCons where
    toConstraint   = bToCons
    fromConstraint = head . consToBs


cand (C u1 b1) (C u2 b2) = C (u1++u2) (b1++b2)
candList cs = foldr cand trueCons cs

remRedundantCons :: Constraint -> Constraint
remRedundantCons (C us bs) = C (removedups2 us) (remRedundantBCons bs)

--------------------------------------------------------------------------------
buildMGU :: Constraint -> E Subst
buildMGU c = unify [] idSubst (buildUP (consToBs c))

buildMGUBCs bcs = unify [] idSubst (buildUP bcs)

-- builds an mgu, not substituing for any variable with a srcId
buildSrcIdMGU :: Constraint -> E Subst
buildSrcIdMGU c = let vs  = filter (hasSrcId . tvarSrcId) (fv c)
		      bcs = consToBs c
		  in  unify vs idSubst (buildUP bcs)

-}
