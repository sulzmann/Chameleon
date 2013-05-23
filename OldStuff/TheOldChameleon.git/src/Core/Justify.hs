--------------------------------------------------------------------------------
--
-- Copyright (C) 2002 The Chameleon Team
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
-- Justifications
--
--------------------------------------------------------------------------------

module Core.Justify (
    module Core.Justify, module AST.LocInfo, Loc
) where

import List (nub)

import Misc 
import AST.LocInfo
import AST.SrcInfo

--------------------------------------------------------------------------------

-- NOTE: It's *critical* that:  j == (read . show) j
--       (We use this trick to encode justifications, pass them to C/Herbie,
--	  get them back - untouched - and then decode them.)
newtype Just = J [Loc]
    deriving (Eq,Show,Read)

justLocs :: Just -> [Loc]
justLocs (J ls) = ls

instance Pretty Just where
    pretty (J ls) = show ls

noJust :: Just
noJust = J []

nullJust :: Just -> Bool
nullJust (J []) = True
nullJust _	= False

inJust :: Loc -> Just -> Bool
inJust l (J ls)	= l `elem` ls

locToJust :: Integral l => l -> Just
locToJust l = J [fromIntegral l]

locsToJust :: [Loc] -> Just
locsToJust ls = J ls

----------------------------------------

-- Class of things which contain, or represent, a justification.
class Justified a where
    -- extracts the justification
    getJust :: a -> Just 

    -- applies a justification-transforming function
    modJust :: (Just -> Just) -> a -> a

    -- returns the result of applying a function to the justification
    appJust :: (Just -> b) -> a -> b

    -- defaults
    appJust f = f . getJust
--  getJust = error "BUG: getJustLocs not defined for some type"
--  modJust = error "BUG: modJustLocs not defined for some type"

-- replace justification, usually you'd use `withJustOf' instead
reJust :: Justified a => Just -> a -> a
reJust j = modJust (const j)

getJustLocs :: Justified a => a -> [Loc]
getJustLocs = justLocs . getJust

appJustLocs :: Justified a => ([Loc] -> b) -> a -> b
appJustLocs f = f . getJustLocs

modJustLocs :: Justified a => ([Loc] -> [Loc]) -> a -> a
modJustLocs f = modJust (\(J ls) -> J (f ls))

instance Justified Just where
    getJust = id
    modJust = ($)
    appJust = ($)

instance Justified Loc where
    getJust l = J [l]
    modJust   = bug "modJust not defined for type Loc"

instance Justified a => Justified [a] where
    getJust = concatJusts . map getJust
    modJust f = map (modJust f)

instance (Justified a, Justified b) => Justified (a,b) where
    getJust (a,b)   = getJust a `appendJust` getJust b
    modJust f (a,b) = (modJust f a, modJust f b)

nubJust :: Justified a => a -> a
nubJust = modJustLocs nub

-- appends justification of b to (end of) a 
appendJust, appendJustOf :: (Justified a, Justified b) => a -> b -> a
appendJust a b = (++(getJustLocs b)) `modJustLocs` a 
appendJustOf   = appendJust

-- prepends justification of b to (beginning of) a
prependJust, prependJustOf :: (Justified a, Justified b) => a -> b -> a
prependJust a b = ((getJustLocs b)++) `modJustLocs` a 
prependJustOf   = prependJust

-- returns a, with the justification of b
withJust, withJustOf :: (Justified a, Justified b) => a -> b -> a
withJust a b = (const (getJust b)) `modJust` a
withJustOf = withJust

-- test if first justification is a subset of second
subJust :: (Justified a, Justified b) => a -> b -> Bool
subJust a b = getJustLocs a `subset` getJustLocs b

concatJusts :: Justified a => [a] -> Just
concatJusts = foldl appendJust noJust 

unionJusts :: (Justified a, Justified b) => a -> b -> Just
unionJusts a b = nubJust (getJust (appendJust a b))

----------------------------------------
-- special-purpose justifications

-- Justification given to administrative (marked) constraints, which represent
-- annotated or non-recursive functions.
adminLoc  = -2 :: Loc
adminJust = J [adminLoc]

-- Justification given to marked constraints which represent unannotated,
-- mono-recursive functions.
monoAdminLoc  = -3 :: Loc
monoAdminJust = J [monoAdminLoc]


-- used to identify Herbrand constraints which are desugared `True' constraints
trueLoc  = -4 :: Loc
trueJust = J [trueLoc]

-- indicates a herbrand constraint that was used to break a mono. rec. cycle
-- (as distinct from a unicycle)
monoCycleLoc  = -5 :: Loc
monoCycleJust = J [monoCycleLoc]

-- used to uniquely identify a constraint used to skolemise some variable
-- (see e.g. Core.ConsOps minGroundingSubset)
skolConsLoc  = -6 :: Loc
skolConsJust = J [skolConsLoc]

----------------------------------------

instance Justified SrcInfo where
    getJust s = locToJust (srcLoc s)

