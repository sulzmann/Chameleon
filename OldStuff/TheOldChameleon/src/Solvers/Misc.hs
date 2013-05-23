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
-- Miscellaneous Herbie and solver ops.
--
--------------------------------------------------------------------------------

module Solvers.Misc 
where

import List
import Monad
import Foreign.C

import Misc
import Solvers.HsHerbie
import Solvers.Herbrand

--------------------------------------------------------------------------------

-- True if the term represents an implication
isICons :: Herb s c => c -> Herbrand s Bool
isICons tm = do
    (func, arity) <- functor tm
    if (arity /= 3) then return False
      else do
	isC <- isCnst func
	when (not isC) (bug "isICons: functor is not a constant!")
	cstr <- cnstName func
	str  <- doIO (peekCString cstr)
	return (str == "IMP!")

-- True if the term represents an equation
isBCons :: Herb s c => c -> Herbrand s Bool
isBCons tm = do
    (func, arity) <- functor tm
    if (arity /= 2) then return False
      else do
	isC <- isCnst func
	when (not isC) (bug "isBCons: functor is not a constant!")
	cstr <- cnstName func
	str  <- doIO (peekCString cstr)
	return (str == "=")

--------------------------------------------------------------------------------

-- takes a term representing a contraint and returns all its arguments
conArgs :: Herb s c => c -> Herbrand s [c]
conArgs tm = do
    (func,arity) <- functor tm
    mapM (\n -> arg tm n >>= deref) [1..arity]

-- takes a term representing a constraint (user or herbrand), and returns the
-- terms corresponding to variables
fvCons :: (Eq c, Herb s c) => c -> Herbrand s [c]
fvCons tm = do
    (func,arity) <- functor tm
    ts <- args arity []
    vs <- mapM fvType ts
    return (nub (concat vs))
  where
    args 0 as = return as
    args n as = do a <- arg tm n
		   args (n-1) (a:as)

-- as above, but does not include implications
fvNonICons :: (Eq c, Herb s c) => c -> Herbrand s [c]
fvNonICons tm = do
    isI <- isICons tm
    if isI then return []
	   else fvCons tm

-- as above, but finds free variables in a term representing a type
fvType :: Herb s c => c -> Herbrand s [c]
fvType t = fv [] t
  where
    fv vs t0 = do 
	t <- deref t0
	isV <- isVar t
	if isV then return (t:vs)
	  else do
	    isC <- isCnst t
	    if isC then return vs
	      else do
		-- Admiral Ackbar sez: It's an app!
		tm_l <- appArg t 0
		tm_r <- appArg t 1
		vs'  <- fv vs  tm_l
		vs'' <- fv vs' tm_r
		return vs''

-- This is like `fvType', but it does not dereference variables!
fvTypeOrig :: Herb s c => c -> Herbrand s [c]
fvTypeOrig t = fv [] t
  where
    fv vs t = do 
	isV <- isVar t
	if isV then return (t:vs)
	  else do
	    isC <- isCnst t
	    if isC then return vs
	      else do
		-- Admiral Ackbar sez: It's an app!
		tm_l <- appArg t 0
		tm_r <- appArg t 1
		vs'  <- fv vs  tm_l
		fv vs' tm_r
