--------------------------------------------------------------------------------
-- CHRState.hs -- Defines a CHR store.
-- Copright (C) 2004 Gregory J. Duck
-- (Modified/Improved by The Chameleon Team)
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
-- 
-- You should have received a copy of the GNU General Public License
-- along with this program; if not, write to the Free Software
-- Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA 
--
--------------------------------------------------------------------------------

module Solvers.CHRState 
where

import List
import Foreign.C
-- import Data.FiniteMap
import Data.Map

import Solvers.Herbrand
import Core.Justify
import AST.LocInfo
import qualified Core.BCons (BCons)
import qualified Core.UCons (UCons)
import qualified Core.Types (Type,Var)

--------------------------------------------------------------------------------

-- Things used by the CHR state.
type Id           = CInt
data UCons c      = UCons c CInt c Just
data BCons c      = BCons c Just
data HCons c      = HActive 
		  | HCons (UCons c)

-- just for debugging purposes
instance Show (HCons c) where
    show HActive = "HActive"
    show (HCons _) = "HCons"
		  
data OccSort      = Kill 
		  | Remain 
		    deriving Eq
data Occ c        = Occ Id OccSort c [HCons c] (Stack c) Bool
data Occs c       = Occs c CInt [Occ c]
type Progs c	  = [Prog c]
type Prog c       = [Occs c]
data StackCons c  = BuiltinCons [BCons c] 
		  | UserCons (UCons c) 
		  | Numbered (UCons c) Id 
		  | Active (UCons c) Id [Occ c]
data UStoreCons c = Num (UCons c) Id
type Stack c      = [StackCons c]
type UStore c     = [UStoreCons c]
type Matching c   = [UCons c]
type Entry        = [Id]
-- type History      = FiniteMap Entry ()
type History      = Map Entry ()

-- user constraints which have been simplified
type DelStore c	  = [UStoreCons c]

-- contains all of the Herbrand constraints added to the store
type BStore = [Core.BCons.BCons]

-- A list of all the variables in user and herbrand constraints in the 
-- *initial* store (placed there by `createGoal'). 
type Vars c = [c]

-- Combines all of the state which is not part of the core of the CHR solver.
data ExtraState c = Extra { extraDelStore :: DelStore c, 
			    extraBStore :: BStore, 
			    extraVars :: Vars c,
			    extraTopVars :: Vars c,
			    extraLocInfo :: LocInfo,
			    extraMatches :: Matches }
initExtraState = Extra [] [] [] [] emptyLocInfo []

-- The CHR state data type.
-- State	: so-far successful derivation
-- Failed	: failed derivation (no specific cause)
-- FailedBS	: failed due to an unsatisfiable store
-- FailedUniv	: some universally-quantified variable is instantiated
-- FailedUnivEsc: a universally-quantified variable escaped
-- FailedImp	: some implication unsolved (couldn't add anything new)
data State c = -- State (Stack c) (UStore c) (DelStore c) BStore History Id 
	       --	     (Vars c) EvInfo
	       State (Stack c) (UStore c) History Id (ExtraState c)
	     | Failed
	     | FailedBS BStore
	     | FailedUniv BStore Core.Types.Var [Core.Types.Var]
	     | FailedUnivEsc BStore Core.Types.Type [Core.Types.Var]
	     | FailedUCUnmatched Core.UCons.UCons
	     | FailedImp

-- The CHR state monad.
newtype CHR s c a = CHR((State c) -> Herbrand s (State c,a))
instance Monad (CHR bs bc) where 
    (CHR p) >>= k = CHR ( \s0 -> do (s1, a) <- p s0
				    case k a of
					CHR q -> q s1 )
    return a = CHR(\s -> return (s, a))

doHerbrand herb = CHR (\s -> do res <- herb
                                return (s,res))

runCHR s (CHR f) = f s >>= \(_,a) -> return a
runCHRInit (CHR f) = f Failed >>= \(_,a) -> return a

getState :: CHR s c (State c)
getState = CHR (\s -> return (s,s))

putState :: State c -> CHR s c ()
putState state = CHR (\s -> return (state,()))

--------------------------------------------------------------------------------
-- misc.

getBuiltinCons :: Stack c -> [BCons c]
getBuiltinCons s = concat [ bcs | BuiltinCons bcs <- s ]
    
