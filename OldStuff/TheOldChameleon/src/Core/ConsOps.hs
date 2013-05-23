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
-- Operations on constraints.
--
-- Includes:
--  - sat test
--  - finding a min. unsat. subset
--  - finding a min. grounding subset
--  - finding a min. instantiating subset
--  - projecting constraints on variables
--
--------------------------------------------------------------------------------

module Core.ConsOps (
    sat, unsat,
    minUnsatSubset, maxSatSubset, minGroundingSubset, 
    minInstantiatingSubset, findInstantiated,
    dropSkol, project, minImplicantSubset
) where

import List
import Monad
import Maybe

import Misc

import Core.Name
import Core.Types
import Core.Justify
import Core.BuiltIn
import Core.Solver
import Core.CHR
import Core.ICons
import Core.Constraint

import Solvers.Herbrand
import Solvers.Convert

--------------------------------------------------------------------------------

-- Returns True if the constraints are satisfiable
sat :: [BCons] -> IO Bool
sat bcs = do
    st <- newStore
    ok <- runHerbrand st (do
	(_, tjs) <- thread intBCons emptyVarMap bcs
	let ts = map fst tjs
	solveAll ts)
    deleteStore st
    return ok

unsat :: [BCons] -> IO Bool
unsat bcs = do 
    ok <- sat bcs
    return (not ok)

--------------------------------------------------------------------------------

-- Solve and project bcons onto the given variables
project :: [BCons] -> [Var] -> IO (Maybe [Type])
project bcs [] = return (Just [])
project bcs vs = do
    st <- newStore
    mts <- runHerbrand st (do
	(vm, tjs) <- thread intBCons emptyVarMap bcs
	let ts = map fst tjs
	ok <- solveAll ts
	if not ok 
	  then return Nothing
	  else do
	    let mtms = map (\v -> lookupVarMap v vm) vs
	    if any isNothing mtms
	      then return Nothing
	      else do
		let tms = map fromJust mtms
		ts <- mapM (extTypeViaVarMap vm) tms
		return (Just ts)
	    )
    deleteStore st
    return mts


--------------------------------------------------------------------------------

{-
-- Tests if the implication is true under the given CHRs. 
-- NOTE: Only holds if the constraint has no nested implications.
checkImplication :: [CHR] -> ICons -> IO Bool
checkImplication chrs (IC vs d@(lucs,lbcs) c@(rucs,rbcs,_) j) = do
    -- Perform D -->^* D'
    let goal_d = InfGoal "" False [] (lucs /\ lbcs)
    ress <- runInfGoals chrs goal
    case ress of
      (res:_) | isFailure res -> return False
      (InfSuccess _ _ d':_) -> do
	-- 
	undefined
-}    

--------------------------------------------------------------------------------

-- Given an unsatisfiable set of constraints, finds one minimal unsatisfiable
-- subset.
minUnsatSubset :: [BCons] -> IO [BCons]
minUnsatSubset bcs = do
    st  <- newStore 
    min <- runHerbrand st (do
	    -- first internalise all the BCons
	    (_, tjs) <- thread intBCons emptyVarMap bcs
	    let ts = map fst tjs
		cs = zip bcs ts
	    accum cs [])
    deleteStore st
    return min
    
  where
    -- The hs are constraints definitely in the min. unsat. subset (they are
    -- present in the store) - cs need further processing.
    accum :: Herb s c => [(BCons, c)] -> [BCons] -> Herbrand s [BCons]
    accum cs hs = do
	cp <- createCP
	((h,d),cs') <- find cs []
	rewind cp
	-- re-add d to the store, if it becomes unsat., we've found the min.
	-- unsat. subset (d:ds)
	ok <- solveEq d
	if ok then -- not unsatisfiable yet
		   accum cs' (h:hs)

	      else -- it's unsatisfiable, we're done
		   return (h:hs)
	
      where
	-- Finds the next constraint to add to the min. unsat. subset.
	-- Go through cs until the store becomes unsat.
	-- Returns both the constraint definitely in the min. unsat. subset, as
	-- well as the rest of the constraints to consider.
	find :: Herb s c => [(BCons, c)] -> [(BCons, c)]
	     -> Herbrand s ((BCons,c), [(BCons, c)])
	find [] _ = bug "minUnsatSubset: constraint not unsat!"
	find (hc@(_,c):cs) as = do
	    ok <- solveEq c
	    if ok
	      then -- not unsatisfiable yet
		   find cs (hc:as)

	      else -- unsatisfiable with the addition of this constraint
		   return (hc, as)
		

-- Solves all given equations, as represented by terms, returns True if
-- successful, else False (note: no binding is undone)
solveAll :: Herb s c => [c] -> Herbrand s Bool
solveAll [] = return True
solveAll (t:ts) = do
    ok <- solveEq t
    if not ok then return False
	      else solveAll ts

-- Unifies left and right sides of given equation, returns True if
-- successful, else False (note: no binding is undone)
solveEq :: Herb s c => c -> Herbrand s Bool
solveEq tm = do
    t1 <- arg tm 1
    t2 <- arg tm 2
    stat <- unify t1 t2
    return (not (failed stat))
    
----------------------------------------

-- finds a maximal satisfiable subset of the given constraints
maxSatSubset :: [BCons] -> IO [BCons]
maxSatSubset bcs = do
    st  <- newStore
    max <- runHerbrand st (do
	    -- first internalise all the BCons
	    (_, tjs) <- thread intBCons emptyVarMap bcs
	    let ts = map fst tjs
	    bs <- check ts
	    return [ bc | (ok,bc) <- zip bs bcs, ok ] )
    deleteStore st
    return max
  where
    check [] = return []
    check (t:ts) = do
	cp <- createCP
	ok <- solveEq t
	rewind cp
	if ok 
	  then do
	    solveEq t
	    oks <- check ts
	    return (ok:oks)
	  else do
	    oks <- check ts
	    return (ok:oks)

----------------------------------------

-- Finds a minimal subset of bcs1 that implies bcs2.
-- Variables passed in are considered existentially quantified. i.e.
-- `don't care' variables.
-- NOTE: We assume the union of all these constraints is satisfiable!
minImplicantSubset :: [Var] -> [BCons] -> [BCons] -> IO [BCons]
minImplicantSubset evs bcs1 bcs2 = do
    st  <- newStore 
    min <- runHerbrand st ((do
	    -- first internalise all the BCons
	    (vm1, tjs1) <- thread intBCons emptyVarMap bcs1
	    (vm2, tjs2) <- thread intBCons vm1 bcs2
	    (vm3, ts3)  <- thread intVar vm2 evs
	    let ts1 = map fst tjs1
		ts2 = map fst tjs2
		cs = zip bcs1 ts1
	    
	    -- fv(bcs2), before any unification
	    ivs <- concatMapM fvCons ts2    
	    let orig_vs = ivs `without` ts3
	    -- solve bcs2, and find what each iv \in ivs is; we can check if
	    -- the store implies bcs2 by again dereferencing each iv, and
	    -- checking if we get the same result
	    cp <- createCP
	    solveAll ts2
	    orig_ts <- mapM extType orig_vs
	    rewind cp
	    
	    accum orig_vs orig_ts cs []) :: Herbrand Store [BCons])
    deleteStore st
    return min
    
  where
    -- The hs are constraints definitely in the min. unsat. subset (they are
    -- present in the store) - cs need further processing.
    accum :: [Term] -> [Type] -> [(BCons, Term)] -> [BCons] 
	  -> Herbrand Store [BCons]
    accum orig_vs orig_ts cs hs = do
	cp <- createCP
	((h,d),cs') <- find cs []
	rewind cp
	-- re-add d to the store, if it becomes unsat., we've found the min.
	-- unsat. subset (d:ds)
	imp <- stepEq d
	if imp 
	  then -- it's implied, we're done
	       return (h:hs)
	       
	  else -- not implied yet
	       accum orig_vs orig_ts cs' (h:hs)
		   
	
      where
	-- Finds the next constraint to add to the min. unsat. subset.
	-- Go through cs until the store becomes unsat.
	-- Returns both the constraint definitely in the min. unsat. subset, as
	-- well as the rest of the constraints to consider.
	find :: [(BCons, Term)] -> [(BCons, Term)]
	     -> Herbrand Store ((BCons,Term), [(BCons, Term)])
	find [] _ = bug "minImplicantSubset: constraint not an implicant!"
	find (hc@(_,c):cs) as = do
	    imp <- stepEq c
	    if imp
	      then -- implied with the addition of this constraint
		   return (hc, as)

	      else -- not implied yet
		   find cs (hc:as)

    
	-- Adds given constraint to store, 
	stepEq :: Term -> Herbrand Store Bool
	stepEq t = do
	    solveEq t
	    cur_ts <- mapM extType orig_vs
	    return (orig_ts == cur_ts)

----------------------------------------

-- Finds a minimal subset of equations in bcs which grounds a variable v.
-- This works by first skolemising v, then finding a min. unsat. subset.
minGroundingSubset :: Var -> [BCons] -> IO [BCons]
minGroundingSubset v bcs = do
    let sk_bc = (TVar v =+= TCon (mkFreeName "Sk!")) skolConsJust
    min <- minUnsatSubset (sk_bc:bcs)
    return (dropSkol min)

----------------------------------------

-- Finds a minimal subset of equations in bcs which instantiates variable v
-- by either one of the other vs or by some constant.
-- This works by first skolemising vs, then finding a min. unsat. subset.
minInstantiatingSubset :: Var -> [Var] -> [BCons] -> IO [BCons]
minInstantiatingSubset v vs bcs = try sk_vs
  where
    -- skolemises v
    sk_v = (TVar v =+= TCon (mkFreeName "Sk!")) skolConsJust

    -- skolemises vs
    sk_vs = map (\v -> (TVar v =+= TCon (mkFreeName "Sk!!")) skolConsJust) vs
    
    try :: [BCons] -> IO [BCons]
    -- if v isn't instantiated by any of vs, it must already be affected by bcs
    try [] = do
	min <- minUnsatSubset (sk_v:bcs)
	return (dropSkol min)
	     
    try (bc:bcs) = do
	mres <- try1 bc
	case mres of
	    Nothing  -> try bcs
	    Just res -> return res
    
    try1 :: BCons -> IO (Maybe [BCons])
    try1 bc = do
	let bcs' = bc : sk_v : bcs
	ok <- sat bcs'
	if ok then return Nothing
	      else do min <- minUnsatSubset bcs'
		      return (Just (dropSkol min))


--------------------------------------------------------------------------------

-- Finds out which of the variables is instantiated by the given set of
-- constraints (which must be satisfiable.)
findInstantiated :: [BCons] -> [Var] -> IO Var
findInstantiated bcs vs = do
    st <- newStore
    -- first solve all bcs
    (vm,ok) <- runHerbrand st (do
	(vm, tjs) <- thread intBCons emptyVarMap bcs
	let ts = map fst tjs
	ok <- solveAll ts
	return (vm,ok))
    unless ok (bug ("findInstantiated: bcs not sat!\n")) --  ++ pretty bcs))
    v <- runHerbrand st (try vm vs)
    deleteStore st
    return v

  where
    skol v = (TVar v =+= TCon (mkFreeName "Sk!")) skolConsJust

    try vm []     = bug "findInstantiated: no variable instantiated!"
    try vm (v:vs) = do
	    cp <- createCP
	    (_,tj) <- intBCons vm (skol v)
	    ok <- solveEq (fst tj)
	    rewind cp
	    if ok then try vm vs    -- not instantiated
		  else return v	    -- instantiated


--------------------------------------------------------------------------------

-- The first variable escapes through the second.
-- Find the minimal subset of constraints which allows this to happen.
-- (we find a minimal bcs' subset bcs, such that: v1 in fv(mgu(bcs') v2)
minEscapeSubset :: Var -> Var -> [BCons] -> IO [BCons]
minEscapeSubset v1 v2 bcs = do
    -- solve bcs, find fv v2, gen skol constraints, then find min. unsat subset
    st <- newStore
    vs <- runHerbrand st (do
	(vm, tjs) <- thread intBCons emptyVarMap bcs
	let ts = map fst tjs
	    tm2 = case lookupVarMap v2 vm of
		   Nothing -> bug "minEscapeSubset: VarMap must contain v2"
		   Just x  -> x
	mapM_ solveEq ts
	t2 <- extOrigType tm2
	let vs = map (originalVar vm) (fv t2)
	doIO (putStrLn ("t2: " ++ pretty t2))
	doIO (putStrLn ("vs: " ++ pretty vs))
	return vs)
    deleteStore st
	
    let sk_bc  = mkSk2 v1 
	sk_bcs = map mkSk1 vs
	bcs' = sk_bc : sk_bcs ++ bcs

    s <- sat bcs'

    putStrLn ("sk_bc : " ++ pretty sk_bc)
    putStrLn ("sk_bcs: " ++ pretty sk_bcs)
    putStrLn ("bcs' sat? " ++ show s)
	
    min <- minUnsatSubset bcs
    return (dropSkol min)

  where
    mkSk1 x = (TVar x =+= TCon (mkFreeName "Sk!")) skolConsJust
    mkSk2 x = (TVar x =+= TCon (mkFreeName "Sk!!")) skolConsJust


--------------------------------------------------------------------------------

-- remove skolemisation bcs
dropSkol :: [BCons] -> [BCons]
dropSkol = filter ((/=skolConsJust) . getJust)

--------------------------------------------------------------------------------

test m =
{-
    let a = TVar (mkVar "a")
	b = TVar (mkVar "b")
	c = TVar (mkVar "c")
        d = TVar (mkVar "d")
	e = TVar (mkVar "e")
	f = TVar (mkVar "f")
	  
	eq0 = a =:= boolType
	eq1 = a =:= b
	eq2 = b =:= c
	eq3 = c =:= charType 
	eq4 = b =:= d
	eq5 = d =:= e
	eqs = [eq1,eq2,eq3,eq4,eq0]
-}

    let eqs = [TVar (mkVar "V1") =:= boolType] ++
	      [TVar (mkVar ('V' : show (m+1))) =:= charType] ++
	      [ t1 =:= t2 | n <- [1..m], let t1 = TVar (mkVar ('V':show n))
					     t2 = TVar (mkVar ('V':show (n+1)))]
    
    in  eqs

--------------------------------------------------------------------------------

{-
solve :: [BCons] -> IO ()
solve bcs = do
    st <- newStore
    ok <- runHerbrand st (do
	(vm, tjs) <- thread intBCons emptyVarMap bcs
	doIO $ putStrLn ("vm: " ++ pretty (sort (varMapToList vm)))
	let ts = map fst tjs
	doIO $ putStrLn "\nBEFORE"
	mapM_ printTerm ts
	solveAll ts
	doIO $ putStrLn "\n\nAFTER"
	mapM_ printTerm ts )
    deleteStore st
  where
    solveAll [] = return True
    solveAll (t:ts) = do
	ok <- solveEq t
	if not ok then return False
		  else solveAll ts
-}
