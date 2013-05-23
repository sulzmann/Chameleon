--------------------------------------------------------------------------------
--  Herbrand.hs -- Haskell interface to herbie
--  Copright (C) 2004 Gregory J. Duck
--  (Modified/Improved by The Chameleon Team
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License
--  along with this program; if not, write to the Free Software
--  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA 
--------------------------------------------------------------------------------

module Solvers.Herbrand 
where

import Monad
import Foreign
import Foreign.C

import Misc

data UnifyStatus = Success 
		 | MismatchFail 
		 | OccursFail 
		 | MatchingFail
    deriving Eq
    
data HerbrandFlag = NoRewindHeap | NoOccursCheck | NoTrail
data FlagState = On 
	       | Off

type ChoicePointId = CInt

data HerbState store = HerbState store Int

newtype Herbrand store a = Herbrand (HerbState store -> IO (HerbState store,a)) 

instance Monad (Herbrand store) where
    (Herbrand p) >>= k = Herbrand ( \s0 -> do (s1, a) <- p s0
					      case k a of
						Herbrand q -> q s1 )
    return a = Herbrand(\s -> return (s, a))

class Show term => Herb store term | store -> term, term -> store where
    -- Create a new (empty) store.
    newStore :: IO store 

    -- Delete a store.  Implicitly promise never to use that store
    -- again.
    deleteStore :: store -> IO ()
    
    -- Do a unification between two terms.  Note: does not
    -- undo bindings on failure!
    unify :: term -> term -> Herbrand store UnifyStatus
    
    -- Do a partial match between two terms.  Matching is implemented
    -- as one-way unification, which means variables in the first term
    -- are not allowed to become more "bound" than before the matching.
    -- Note: does not undo bindings on failure!  Not to be used in 
    -- conjunction with other Herbrand operations until after the rewinding!
    match :: term -> term -> Herbrand store UnifyStatus

    -- Test if two terms are equal (like Prolog's ==/2, hence the name).
    -- Does not bind variables so there is no need to rewind trail.
    eqeq :: term -> term -> Herbrand store UnifyStatus

    -- Test if two terms are variants.  Note: assumes that all non-existential
    -- variables have been Skolemised.  Must always rewind trail after usage.
    variant :: term -> term -> Herbrand store UnifyStatus
   
    -- Skolemises a variable, i.e. binds the variable to a unique constant.
    -- Note: cnst operations do not work with skolemised variables!
    skolemise :: term -> Herbrand store ()
   
    -- Turn a string (CString) into a constant term.
    cnst :: CString -> Herbrand store term

    -- Turn term1 and term2 into (term1 @ term2), i.e. application.
    app :: term -> term -> Herbrand store term

    -- Return a fresh, unbound variable.
    var :: Herbrand store term

    -- Maps a constant term into a CString.  Note: Assumes the term is a
    -- constant term!
    cnstName :: term -> Herbrand store CString

    -- Returns an argument (either 0 or 1) of an application.  Note: 
    -- Assumes the term is an application!
    appArg :: term -> CInt -> Herbrand store term

    -- Tests if the given term is an unbound variable.
    isVar :: term -> Herbrand store Bool

    -- Tests if the given term is a constant.
    isCnst :: term -> Herbrand store Bool

    -- Tests if the given term is an application.
    isApp :: term -> Herbrand store Bool
    
    -- Tests if the given term is a variable, without dereferencing it.
    wasVar :: term -> Herbrand store Bool
 
    -- Dereference the term.
    deref :: term -> Herbrand store term
    
    -- Creates a copy of the given term with all of the variables renamed
    -- (exactly like Prolog's copy_term/2).  Multiple calls to rename are
    -- allowed in a row, and the result must be as if the renaming occurs
    -- "all at once".  Note: Must create a CP before use and rewind after 
    -- use.  Not to be used in conjunction with other Herbrand operations
    -- until after the rewinding!  Before rewinding, call
    --     setFlag NoRewindHeap On
    -- then
    --     setFlag NoRewindHeap Off
    -- afterwards, got that?
    rename :: term -> Herbrand store term
    
    -- Tests if the given term is ground.
    ground :: term -> Herbrand store Bool
    
    -- Succeeds if the given terms share at least one variable.
    share :: term -> term -> Herbrand store Bool

    -- Create a choicepoint.
    createCP :: Herbrand store ChoicePointId
    
    -- Rewind (undo) all changes to the store since the call to createCP
    -- which created the ID.
    rewind :: ChoicePointId -> Herbrand store ()
    
    -- Sets a flag. 
    setFlag :: HerbrandFlag -> FlagState -> Herbrand store ()
    
    -- Print a term (for debugging)
    printTerm :: term -> Herbrand store ()

    -- Construct a constraint
    construct :: term -> [term] -> Herbrand store term

    -- Like Prolog's functor/3
    functor :: term -> Herbrand store (term,CInt)

    -- Like Prolog's arg/3
    -- (First arg is number 1.)
    arg :: term -> CInt -> Herbrand store term

-- Safely renames a list of terms.
-- This is mainly for documentation pruposes, to show how to use rename safely.
renameList :: Herb store c  => [c] -> Herbrand store [c]
renameList [] = return []
renameList cs = do
    cp <- createCP
    result <- renameList' cs
    setFlag NoRewindHeap On
    rewind cp
    setFlag NoRewindHeap Off
    return result

renameList' :: Herb store c => [c] -> Herbrand store [c]
renameList' []     = return []
renameList' (c:cs) = do
    d <- rename c
    ds <- renameList' cs
    return (d:ds)

-- Succeeds if UnifyStatus indicates failure.
failed :: UnifyStatus -> Bool
failed Success      = False
failed MismatchFail = True
failed OccursFail   = True
failed MatchingFail = True

-- Gets the Herbrand store.
getStore :: Herbrand store store
getStore = Herbrand (\t@(HerbState s n) -> return (t,s))

retState :: Herbrand store (HerbState store)
retState = Herbrand (\s -> return (s,s))

setState :: HerbState store -> Herbrand store ()
setState st = Herbrand (\_ -> return (st,()))

-- Do an IO operation.
doIO io = Herbrand (\s -> do res <- io
                             return (s,res))

runHerbrand :: s -> Herbrand s a -> IO a
runHerbrand s (Herbrand f) = do
    (_,a) <- f (HerbState s 1)
    return a


genSkolemConst :: Herb s t => Herbrand s t
genSkolemConst = do
    HerbState s n <- retState
    cstr <- doIO $ newCString ("SK!" ++ show n)
    sk   <- cnst cstr
    setState (HerbState s (n+1))
    return sk

isSkolemConst :: Herb s t => t -> Herbrand s Bool
isSkolemConst t = do
    n <- cnstName t
    str <- doIO $ peekCString n
    return (str `hasPrefix` "SK!")
