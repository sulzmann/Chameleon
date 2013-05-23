--------------------------------------------------------------------------------
-- Copyright (C) 2005 The Chameleon Team
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
-- Implementor: J. Wazny
--  Maintainer: J. Wazny
--      Status: bugs (see below)
--------------------------------------------------------------------------------
--
-- Invokes the CHR solver in order to solve:
--  1. typing constraints: (see Core.Inference) for W-style inf.
--  2. inference goals: which also express typing constraints, as per CLP-style
--     inf (see Core.CHRGenerator), as well as kind constraints (see
--     Core.Kinds.Inference.)
-- This module contains the `extended' solver, for solving implication
-- constraints, which is defined in terms of the standard CHR solver.
--
-- NOTE: Ideally the Term and Store types should be factored out, as in 
--	 HsHerbie, but currently we only allow the Herbie C terms and store.
--
-- NOTE: Each CHR derivation is run in stages; at the moment this means
-- propagation rules are fully applied first, then simplification rules.
--
--------------------------------------------------------------------------------
-- OLD!
-- BUGS: 
--  - We're letting out constraints from top-level subsumption goals. Obviously
--  such constraints are `unmatched' and should be reported as such.
--  (The only constraints which escape in this way are all ground, e.g. UC Int)
--  Probably the easiest fix is to pass the `nested' flag down to the
--  implication solver. If it's not nested, then the current implication must
--  be a solved form, no partial solution is allowed.
--
--------------------------------------------------------------------------------
--
-- A step-by-step overview of the solving process.
-- 
-- 1. One of solveTypingConstraint, or runInfGoals(LocInfo) is invoked.
-- 
--  a) Constraints, CHR rules (and other elements) are passed-in in terms of 
--  the Haskell data structures in Core.Constraint, Core.Types, Core.CHR and so 
--  on. These are converted to Terms (see the instance of Herb in
--  Solvers.HsHerbie), and Rule Terms (see Solvers.CHRRule), via procedures in 
--  Solvers.Convert. Terms are the Haskell-side representation of Herbrand 
--  terms in the Herbie herbrand solver (see Solvers/herbie.c).
--  This process is known as `internalisation.' See note below.
-- 
--  b) An initial CHR goal is created (see Solver.CHR).
--
-- 2. Solving begins with the extended solver (see extendedSolver)
--
--  a) We always commence with a primitive solving step, i.e. a CHR derivation
--  This is to ensure that any context, when processing an implication, is
--  fully reduced.
--
--  b) If there are implications present, we perform a sequence of general 
--  solving steps, by invoking solveAllImplications, which takes a general step
--  (by calling solveImplication) for each implication present.
--
-- 3. If any implications remain after solving:
--
--  a) and solving failed for any single implication, we fail.
--  
--  b) and there is an implication that yielded no partial solution, we fail.
--
--  c) but all contributed to some partial solution, we return to step 2.
--
-- 4. If no implication remain, i.e. all were found to be in a solved-form wrt.
-- the context, then solving succeeds.
--
-- NOTE: Types and constraints are represented uniformly in the Herbie term
-- representation. All constraints consist of a functor applied to some number
-- of arguments. Herbrand constraints are identified by the functor "=", while
-- implications use "IMP!". All other functors represent so-named user
-- constraint predicate symbols.
--  
--------------------------------------------------------------------------------

module Core.Solver (
    checkImplication,
    solveTypingConstraint,
    runInfGoals, runInfGoalsLocInfo
) where 

import IO
import Monad	hiding (ap)
import Maybe
import List
import qualified Data.Set as Set    --NOTE: changed in GHC 6.4
-- import Data.FiniteMap		    --NOTE: deprecated in GHC 6.4 (use Data.Map)
import Data.Map  hiding (map,partition,filter,null,delete)
import Foreign.C

import Misc
import Core.CHR
import Core.InfGoal
import Core.InfResult
import Core.Types	hiding (rename)
import Core.Constraint
import Core.Justify
import Core.Name
import qualified Core.Evidence as Ev

import Solvers.CHR	    
import Solvers.CHRState	hiding (BCons)
import qualified Solvers.CHRState 
import Solvers.Herbrand hiding (skolemise)
import Solvers.Convert	hiding (skolemise)

import qualified AST.Common as AST

--------------------------------------------------------------------------------

-- Attempting to solve an implication results in one of the following:
--  CantSolve: can't be solved
--  CanRemove: a solved form (wrt the current store); can be removed
--  UpdatedStore: Partially solved; add given user constraints to state store
data ImpStatus = CantSolve
	       | CanRemove
	       | UpdatedStore (UStore Term)

instance Eq ImpStatus where
    (==) s1 s2 = case (s1, s2) of
		      (CantSolve, CantSolve) -> True
		      (CanRemove, CanRemove) -> True
		      (UpdatedStore _, UpdatedStore _) -> True
		      _ -> False


-- Use the following synonyms whenever possible to simplify and keep types
-- consistent.
type CHRResult a = Solvers.CHRState.CHR Store Term a
type CompiledCHRs = Progs Term
type CHRState = State Term
type IConsTerm = UStoreCons Term 
type JTTerm = JTerm Term
type ChoicePoint = CInt

--------------------------------------------------------------------------------
-- Helpers

cPut :: String -> CHRResult ()
cPut = doHerbrand . hPut

hPut :: Herb s c => String -> Herbrand s ()
hPut = doIO . putStrLn

--------------------------------------------------------------------------------

-- Tests if the implication is true under the given CHRs. 
-- Will return a successful result if so, else a failure.
-- NOTE: Only holds if the constraint has no nested implications.
checkImplication :: [Core.CHR.CHR] -> ICons -> IO InfResult
checkImplication chrs0 ic@(IC vs (lucs, lbcs) (rucs, rbcs, _) j) = do
    -- Reorder so that propagation rules appear before simplification.
    let chrs = propsFirst chrs0
    -- Create a new store to do all processing in.
    st  <- newStore
    irs <- runHerbrand st (runCHRInit (do
	    -- Internalise CHRs, see Solvers.Convert.
	    ichrs <- doHerbrand (mapM (intCHR emptyVarMap) chrs)

	    -- Compile CHRs (convert to a form appropriate for CHR solver).
	    prog  <- doHerbrand (compileCHRsNoReorder ichrs)

	    -- Internalise the constraint and solve.
	    (vm, int_ic) <- doHerbrand (intICons emptyVarMap ic)
	    ic_status <- solveSingleImplication [prog] int_ic

	    -- Construct inference results.
	    state <- getState
	    mkInfResult state vm ic_status
	    ))
    -- Delete the store - we're done with it.
    deleteStore st
    return irs
    
  where
    id   = AST.anonId "checkImplication"
    ids  = repeat id
    cons = trueConstraint
  
    -- Externalise the Herbrand variable corresponding to the given type 
    -- variable, and apply the substitution.
    ext :: VarMap -> Subst -> Var -> Herbrand Store Type
    ext vm s v = do
	let mt = lookupVarMap v vm
	case mt of
	    Nothing -> bug "Core.Solver.solveConstraint: v not in vm"
	    Just tm -> do et <- extType tm
			  return (apply s et)
    
    -- Generate an inference result, given 
    mkInfResult :: State Term -> VarMap -> ImpStatus -> CHRResult InfResult
    mkInfResult state vm ic_status = case state of 
	-- From a success state, we can return multiple results.
	State {} | ic_status /= CantSolve -> do 
	    let success = InfSuccess id [] trueConstraint
	    return success
	
	-- All failure cases only return a single result.
	_ -> return $ case state of
	
	    Failed   {} -> InfFailure id cons

	    FailedBS {} -> InfFailure id cons
	    
	    FailedUCUnmatched uc -> InfFailureUConsUnmatched id uc
	    
	    FailedUniv _ v vs -> let v' = originalVar vm v
				 in  InfFailureUniv id v' vs cons
			 
	    FailedUnivEsc _ t uvs -> 
		    let uvs' = map (originalVar vm) uvs
		    in  InfFailureUnivEsc id (head vs) t uvs' cons

	    _ -> InfFailure id cons

-- Solving an individual implication.
-- This constitutes a `General' extended solving step.
-- Given, C0,(\forall as. D \implies C), we compute:
--  1. C0, D -->* D'	    (a CHR derivation)
--  2. D', C >>* C'	    (an extended solver derivation)

-- We then:
--  3. Check C', D' for equivalence, wrt fv(C0,D,as) (as they are in D'). 
--     This is the solved-form check. 
--  
--  If equivalent, we can remove the implication, otherwise:
--  4. We perform abduction; the Add step.
solveSingleImplication :: CompiledCHRs -> JTTerm -> CHRResult ImpStatus
solveSingleImplication chrs (ic, j_ic) = do
    state_c0@(State _ ucs_c0 _ _ extra) <- getState
    -- Disect the implication term into its components: LHS and RHS user and 
    -- herbrand constraints (with justifications), and quantified variables.
    (evs_info,jlucs,jlbcs,jrucs,jrbcs) <- doHerbrand $ disectICons ic
    
    -- 1. Set up and perform D' derivation.
    setupD'Derivation state_c0 jlbcs jlucs
    chrDerivation chrs
    state_d' <- getState
    if isFailedState state_d' 
      then
	-- LHS/D' derivation failed - we can't solve this implication.
	-- ERROR REPORTING NOTE: We keep the unsatisfiable store; the
	-- error is reported as a typical type conflict.
	return CantSolve
      else do
	-- Find significant variables, i.e. fv(C0,D,as), before second
	-- derivation! NOTE: We need to find these now because they may be
	-- instantiated by the C' derivation, and will no longer be
	-- distinguishable as variables from other terms.
	fvs_d'@(fv_c0,fv_d',fv_ex) <- findD'Vars state_c0 state_d' evs_info

	-- 2. Set up and perform C' derivation.
	setupC'Derivation state_c0 state_d' jrbcs jrucs fv_c0 fv_d'
	extendedSolver chrs
	state_c' <- getState
	if isFailedState state_c'
	  then
	    -- RHS/C' derivation failed - we can't solve this implication.
	    -- ERROR REPORTING NOTE: Same as LHS/D' failure case.
	    return CantSolve
	  else do
	      
	    -- 3. Check for equality (implication solved form.)
	    solved <- checkSolvedForm state_d' state_c' fvs_d'
	    if solved then return CanRemove
		      else return CantSolve
  where
    -- Create a fresh goal for the LHS constraints, i.e. for the D' derivation.
    setupD'Derivation state_c0@(State _ ucs_c0 _ _ extra_c0) jlbcs jlucs = do
	let (lucs,jlus) = unzip jlucs
	    (lbcs,jlbs) = unzip jlbcs

	-- Externalise the bcs to add to the bstore.
	lbs <- doHerbrand $ mapM (uncurry extOrigBCons) jlbcs
	
	-- Generate initial goal from lucs, lbcs.
	goal_d@(State s u h i extra_d) <- doHerbrand $ createGoal (lucs ++ lbcs)
								  (jlus ++ jlbs)
	-- Combine this with the user constraints from C0.
	-- ALERT: shouldn't we inherit the dstore in the new goal as well?
	let extra_d' = extra_d { extraBStore = lbs ++ extraBStore extra_c0 ++
					       extraBStore extra_d,
			         extraDelStore = extraDelStore extra_c0,
				 extraTopVars = extraTopVars extra_c0,
			         extraMatches = extraMatches extra_c0,
			         extraLocInfo = extraLocInfo extra_c0 }
	    goal_d' = State (ustoreToStack ucs_c0 ++ s) u h i extra_d'
	putState goal_d'
	

    -- Create a fresh goal for the RHS constraints, i.e. for the D' derivation.
    setupC'Derivation state_c0@(State _ ucs_c0 _ _ extra_c0)
		      state_d'@(State _ ucs_d' _ _ extra_d') 
		      jrbcs jrucs fv_c0 fv_d' = do
	let (rucs,jrus) = unzip jrucs
	    (rbcs,jrbs) = unzip jrbcs
	
	-- Externalise the bcs to add to the bstore.
	rbs <- doHerbrand $ mapM (uncurry extOrigBCons) jrbcs

	-- Remove duplicates from variables
	global_vs <- doHerbrand $ keepVarsNoDeref (fv_c0 ++ fv_d')

	-- Generate initial goal from rucs, rbcs.
	goal_c@(State s u h i extra_c) <- doHerbrand $ createGoal (rucs ++ rbcs)
								  (jrus ++ jrbs)
					
        -- Combine this with the D' result.
	let extra_c' = extra_c { extraBStore = rbs ++ extraBStore extra_d' ++ 
					       extraBStore extra_c,
				 extraDelStore = extraDelStore extra_d',
				 extraVars = global_vs ++ extraVars extra_c,
				 extraTopVars = extraTopVars extra_d',
				 extraMatches = extraMatches extra_d',
				 extraLocInfo = extraLocInfo extra_d'  }
	    goal_c' = State (ustoreToStack ucs_d' ++ s) u h i extra_c'
	putState goal_c'

    -- Find C0 variables i.e. fv(C0), before any derivations are performed.
    findC0Vars state_c0@(State _ ucs_c0 _ _ extra_c0) = doHerbrand $ do
	vs_c0 <- findC0UconsVars ucs_c0
	keepVarsNoDeref (vs_c0 ++ extraVars extra_c0)

    -- Find significant variables, i.e. fv(C0,D,as) in D'.
    -- NOTE: Call this as soon as we have D', but before C' is calculated.
    findD'Vars state_c0@(State _ ucs_c0 _ _ extra_c0) 
	       state_d'@(State _ ucs_d' _ _ extra_d') evs_info = do
	
	vs_c0 <- doHerbrand $ do
			vs_c0 <- findC0UconsVars ucs_c0
			keepVarsNoDeref (vs_c0 ++ extraVars extra_c0)
	vs_d' <- doHerbrand $ keepVarsNoDeref (extraVars extra_d')
	vs_ex <- doHerbrand $ do
		tvs <- mapM extVarInfo evs_info
		let (evs, _) = unzip tvs
		keepVarsNoDeref evs

	return (vs_c0, vs_d', vs_ex)


    -- Extracts relevant information from the states to call the solved form
    -- check procedure.
    checkSolvedForm state_d'@(State _ ucs_d' _ _ extra_d')
                    state_c'@(State _ ucs_c' _ _ extra_c') 
		    (fv_c0, fv_d', fv_ex) = do
	
	-- Extract justified uc terms from states.
	let tjs_d' = map unwrapUStoreCons ucs_d'
	    tjs_c' = map unwrapUStoreCons ucs_c'

	-- Combine vars.
	let vs = nub (fv_c0 ++ fv_d' ++ fv_ex) 
	isSolvedForm vs tjs_d' tjs_c'


--------------------------------------------------------------------------------

-- Solves a typing constraint, given:
-- 
-- chrs0: The set of CHR rules.
-- idvs: A list of identifier, variable pairs; the identifier is the name of
--	a function whose type we are inferring, the variable represents that 
--	type.
-- free_vs: A list of free variables. These are the variables present in the
--	type environment just prior to invoking the solver. NOTE: we pass these 
--	in because the solver may rename these variables in the	result it 
--	returns; we need to establish a connection between the original names 
--	(that the type inferencer knows) and the renamings.
-- top_vs: A list of top-level variables. During implication solving, we need 
--	to ensure that no quantified variable escapes via one of these.
-- linfo: A data structure (see AST.LocInfo) categorising each program
--	location. This is needed to ensure user constraint matching yields a
--	result that can be used to build evidence.
-- c: The constraint to solve.
--
-- This procedure returns, a triple consisting of:
-- inf results: A list of inference results (see Core.InfResult); these either
--	pair an identifier with its inferred type, or represent a type error.
-- types: These are the renamed free_vs from the input. These can be used to
--	generalise the inferred types.
-- matches: User constraint matches that can be used to build evidence.
solveTypingConstraint :: [Core.CHR.CHR] -> [(AST.Id,Var)] -> [Var] -> [Var] ->
		LocInfo -> Constraint -> IO ([InfResult], [Type], Matches)
solveTypingConstraint chrs0 idvs free_vs top_vs linfo c = do
    -- Reorder so that propagation rules appear before simplification.
    let chrs = propsFirst chrs0
    -- Create a new store to do all processing in.
    st  <- newStore
    irs <- runHerbrand st (runCHRInit (do
	    -- internalise CHRs, see Solvers.Convert 
	    ichrs <- doHerbrand (mapM (intCHR emptyVarMap) chrs)

	    -- compile CHRs (convert to a form appropriate for CHR solver)
	    prog  <- doHerbrand (compileCHRsNoReorder ichrs)

	    -- Internalise: the constraint to solve, the free variables, and
	    -- the top-level variables.
	    let top_vs' = map snd idvs ++ top_vs 
	    (vm1, itjs) <- doHerbrand (intConstraint emptyVarMap c)
	    (vm2, _)  <- doHerbrand (thread intVar vm1 free_vs)
	    (vm, its) <- doHerbrand (thread intVar vm2 top_vs')

	    -- Set up initial state and call the extended solver.
	    setupInitialState linfo its [prog] itjs
	    -- state <- solver [prog]
	    extendedSolver [prog]
	    state <- getState

	    -- Get any user constraints/implications left in the store.
	    (ucs,ics) <- doHerbrand $ getCons state
	    
	    -- Look up the value of each of the original vars, and
	    -- generate a corresponding equation for each; cons is the final
	    -- set of constraints: the remaining user constraints/implications,
	    -- the newly generated equations, and the `built-in' constraint
	    -- store (bstore) accumulated during solving.
	    vts <- doHerbrand $ lookupVars vm
	    let bcs  = map mkEq vts
		cons = ics /\ ucs /\ bcs /\ getBStore state

	    -- NOTE: We build a substitution to map renamed 
	    -- variables back to their original Haskell-side names.
	    rvm <- doHerbrand (mkRevVarMap vm)
	    let subst = buildSubst rvm
	    
	    -- Construct inference results.
	    res <- mkInfResult subst vm cons state

	    -- Find free variable renamings.
	    ren_ts <- doHerbrand (mapM (ext vm subst) free_vs)
	    
	    -- Extract ucons matches from state.
	    let ms = getMatches state

	    return (res,ren_ts,ms)
	    ))
    -- Delete the store - we're done with it.
    deleteStore st
    return irs
    
  where

    ids = map fst idvs
    vs  = map snd idvs
    id   = AST.anonId "W-inf."
  
    -- Externalise the Herbrand variable corresponding to the given type 
    -- variable, and apply the substitution.
    ext :: VarMap -> Subst -> Var -> Herbrand Store Type
    ext vm s v = do
	let mt = lookupVarMap v vm
	case mt of
	    Nothing -> bug "Core.Solver.solveConstraint: v not in vm"
	    Just tm -> do et <- extType tm
			  return (apply s et)
    
    -- Generate an inference result, given 
    mkInfResult :: Subst -> VarMap -> Constraint -> State Term
		-> CHRResult [InfResult]
    mkInfResult subst vm cons state = case state of 
	-- From a success state, we can return multiple results.
	State {} -> do 
	    ts <- doHerbrand (mapM (ext vm subst) vs)
	    (ucs,_) <- doHerbrand (getCons state)
	    let ucs' = apply subst ucs
	        rs   = map (mkSuccess ucs') (zip ids ts)
	    return rs
	  where
	    mkSuccess ucs (i,t) =
	        let vs   = fv t
		    ucs' = [uc | uc <- ucs, let vs' = fv uc, any (`elem`vs) vs']
	        in  InfSuccessW i t ucs'
	
	-- All failure cases only return a single result.
	_ -> (return . (:[])) $ case state of
	
	    Failed   {} -> InfFailure id cons

	    FailedBS {} -> InfFailure id cons
	    
	    FailedUCUnmatched uc -> InfFailureUConsUnmatched id uc
	    
	    FailedUniv _ v vs -> let v' = originalVar vm v
				 in  InfFailureUniv id v' vs cons
			 
	    FailedUnivEsc _ t uvs -> 
		    let uvs' = map (originalVar vm) uvs
		    in  InfFailureUnivEsc id (head vs) t uvs' cons
    
--------------------------------------------------------------------------------

-- Generates and sets the initial solver state.
-- NOTE: This should be called once, before the solver itself is invoked.
setupInitialState :: LocInfo -> [Term] -> Progs Term -> [JTTerm] -> CHRResult ()
setupInitialState linfo t0s progs tjs = do
    -- Create a new state containing the fresh goal constraints.
    let (ts,js) = unzip tjs
    goal@(State s _ _ _ _) <- doHerbrand $ createGoal ts js
    -- We also need to add any equations in the initial goal to the BStore.
    let sbcs = getBuiltinCons s
    bcs <- doHerbrand $ mapM (uncurry extOrigBCons)  
    	    [ (t, j) | Solvers.CHRState.BCons t j <- sbcs ]
    let goal'   = addToBStore bcs goal
	goal''  = setLocInfo linfo goal'
	goal''' = setTopVars t0s goal''
    putState goal'''


-- Generates and sets a simplified initial solver state.
-- NOTE: This should be called once, before the solver itself is invoked.
setupSimpleInitialState :: [Term] -> Progs Term -> [JTTerm] -> CHRResult ()
setupSimpleInitialState t0s progs tjs = do
    -- Create a new state containing the fresh goal constraints.
    let (ts,js) = unzip tjs
    goal@(State s _ _ _ _) <- doHerbrand $ createGoal ts js
    -- We also need to add any equations in the initial goal to the BStore.
    let sbcs = getBuiltinCons s
    bcs <- doHerbrand $ mapM (uncurry extOrigBCons)  
    	    [ (t, j) | Solvers.CHRState.BCons t j <- sbcs ]
    let goal'  = addToBStore bcs goal
	goal'' = setTopVars t0s goal'
    putState goal''

--------------------------------------------------------------------------------

chrDerivation :: CompiledCHRs -> CHRResult ()
chrDerivation = stagedDerivation

--------------------------------------------------------------------------------

-- The extended solver; handles constraints containing implications.
-- There are two cases to handle:
--  1. Primitive: applies when no implications present - just a CHR derivation
--  2. General: solve each implication in turn.
-- NOTE: We always commence with a primitive step to ensure that the context is
-- fully reduced before handling any implications.
extendedSolver :: CompiledCHRs -> CHRResult ()
extendedSolver progs = do
    -- Return any user constraints from the `ustore' to the stack, and perform
    -- a primitive derivation.
    reassertStateUCons
    chrDerivation progs
    state <- getState
    unless (isFailedState state) $ do
	(state',ics) <- extractICons state
	unless (null ics) $ do
	    -- Assert updated state and solve all implications.
	    putState state'
	    -- Now perform a sequence of General/implication solving steps.
	    solveAllImplications progs ics

-- Removes implications, and returns them and the new, smaller state.
extractICons :: CHRState -> CHRResult (CHRState, [UStoreCons Term])
extractICons state@(State s u h id x) = do
    (ucs,ics) <- doHerbrand $ splitUConsICons state
    let state' = State s ucs h id x
    return (state', ics)

----------------------------------------

-- Return any user constraints from the `ustore' to the stack.
-- We need to do this before starting a new derivation with the result of
-- the previous one. (This is safe even if this is the first derivation.)
reassertStateUCons :: CHRResult ()
reassertStateUCons = do
    st <- getState
    case st of
	State s u h id x -> putState (State (ustoreToStack u ++ s) [] h id x)
	_ -> return ()

-- Add given icons to the state in preparation for re-processing.
assertICons :: [IConsTerm] -> CHRResult ()
assertICons ics = do
    st <- getState
    case st of
	State s u h id x -> putState (State (ustoreToStack ics ++ s) [] h id x)
	_ -> return ()

--------------------------------------------------------------------------------

-- Attempt to solve all given implications.
-- Note that the context constraints are implicit -- part of the CHR state.
-- In terms of the extended solver, this procedure continuously performs
-- General solving steps until either:
-- - an error occurs
-- - all implications are reduced
-- - some implication yields no partial solution
solveAllImplications :: CompiledCHRs -> [IConsTerm] -> CHRResult ()
solveAllImplications progs ics = solve ics []
  where
    -- Solve each implication in turn, accumulate unsolved in acc.
    solve [] acc | null acc  = return ()
		 | otherwise = -- Some implications remain, restart with them.
			       solve acc []
    solve (ic:ics) acc = do
	-- Attempt to solve the implication ic -- a General solving step.
	status <- solveImplication progs ic
	case status of
	    CantSolve -> return ()
	    CanRemove -> solve ics acc
	    UpdatedStore ucs -> solve ics (ic:acc)


--------------------------------------------------------------------------------

-- Solving an individual implication.
-- This constitutes a `General' extended solving step.
-- Given, C0,(\forall as. D \implies C), we compute:
--  1. C0, D -->* D'	    (a CHR derivation)
--  2. D', C >>* C'	    (an extended solver derivation)

-- We then:
--  3. Check C', D' for equivalence, wrt fv(C0,D,as) (as they are in D'). 
--     This is the solved-form check. 
--  
--  If equivalent, we can remove the implication, otherwise:
--  4. We perform abduction; the Add step.
solveImplication :: CompiledCHRs -> IConsTerm -> CHRResult ImpStatus
solveImplication chrs ic_j = do
    cPut "solveImplication"
    state_c0@(State _ ucs_c0 _ _ extra) <- getState
    -- Create a choice point.
    cp <- doHerbrand createCP
    -- Remember the C0 variables as they were before any sub-derivation.
    -- Any partial solution will be phrased in terms of these variables.
    orig_fv_c0 <- findC0Vars state_c0
    
    -- Disect the implication term into its components: LHS and RHS user and 
    -- herbrand constraints (with justifications), and quantified variables.
    let (ic, j_ic) = unwrapUStoreCons ic_j
    (evs_info,jlucs,jlbcs,jrucs,jrbcs) <- doHerbrand $ disectICons ic
    
    -- 1. Set up and perform D' derivation.
    setupD'Derivation state_c0 jlbcs jlucs
    chrDerivation chrs
    state_d' <- getState
    if isFailedState state_d' 
      then
	-- LHS/D' derivation failed - we can't solve this implication.
	-- ERROR REPORTING NOTE: We keep the unsatisfiable store; the
	-- error is reported as a typical type conflict.
	subderivationFailed cp
      else do
	-- Find significant variables, i.e. fv(C0,D,as), before second
	-- derivation! NOTE: We need to find these now because they may be
	-- instantiated by the C' derivation, and will no longer be
	-- distinguishable as variables from other terms.
	fvs_d'@(fv_c0,fv_d',fv_ex) <- findD'Vars state_c0 state_d' evs_info
{-
	cPut "-------------- D' -------------------"
	cPut "fv_c0:"
	mapM_ (cPut . show) fv_c0
	cPut "dereferenced fv_c0:"
	doHerbrand $ mapM_ printTerm fv_c0
	cPut "fv_ex:"
	mapM_ (cPut . show) fv_ex
	cPut "dereferenced fv_ex:"
	doHerbrand $ mapM_ printTerm fv_ex
-}	  
	-- 2. Set up and perform C' derivation.
	setupC'Derivation state_c0 state_d' jrbcs jrucs fv_c0 fv_d'
	extendedSolver chrs
	state_c' <- getState
	if isFailedState state_c'
	  then
	    -- RHS/C' derivation failed - we can't solve this implication.
	    -- ERROR REPORTING NOTE: Same as LHS/D' failure case.
	    subderivationFailed cp
	  else do
{-
	    cPut "-------------- C' -------------------"
	    cPut "fv_c0:"
	    mapM_ (cPut . show) fv_c0
	    cPut "dereferenced fv_c0:"
	    doHerbrand $ mapM_ printTerm fv_c0
	    cPut "fv_ex:"
	    mapM_ (cPut . show) fv_ex
	    cPut "dereferenced fv_ex:"
	    doHerbrand $ mapM_ printTerm fv_ex
-}
	      
	    -- 3. Check for equality (implication solved form.)
	    solved <- checkSolvedForm state_d' state_c' fvs_d'
	    if solved 
	      then do	-- Solved form - drop the implication.
	        -- cPut "SOLVED FORM"
		doHerbrand $ rewindMaintainHeap cp
		return CanRemove
	      else do	
		-- cPut "NOT A SOLVED FORM"
		-- 4. Not a solved form, extract a partial solution.
		-- This is the Add step of the extended solver.
		sol<-findPartialSolution (ic,j_ic) fv_c0 fv_ex state_d' state_c'
		let rewind = doHerbrand (rewindMaintainHeap cp)
		handlePotentialPartialSolution rewind state_c0 state_c' 
			orig_fv_c0 fvs_d' j_ic sol

  where
    subderivationFailed :: ChoicePoint -> CHRResult ImpStatus
    subderivationFailed cp = do
	doHerbrand (rewindMaintainHeap cp) 
	return CantSolve
  
    -- Create a fresh goal for the LHS constraints, i.e. for the D' derivation.
    setupD'Derivation state_c0@(State _ ucs_c0 _ _ extra_c0) jlbcs jlucs = do
	let (lucs,jlus) = unzip jlucs
	    (lbcs,jlbs) = unzip jlbcs

	-- Externalise the bcs to add to the bstore.
	lbs <- doHerbrand $ mapM (uncurry extOrigBCons) jlbcs
	
	-- Generate initial goal from lucs, lbcs.
	goal_d@(State s u h i extra_d) <- doHerbrand $ createGoal (lucs ++ lbcs)
								  (jlus ++ jlbs)
	-- Combine this with the user constraints from C0.
	-- ALERT: shouldn't we inherit the dstore in the new goal as well?
	let extra_d' = extra_d { extraBStore = lbs ++ extraBStore extra_c0 ++
					       extraBStore extra_d,
			         extraDelStore = extraDelStore extra_c0,
				 extraTopVars = extraTopVars extra_c0,
			         extraMatches = extraMatches extra_c0,
			         extraLocInfo = extraLocInfo extra_c0 }
	    goal_d' = State (ustoreToStack ucs_c0 ++ s) u h i extra_d'
	putState goal_d'
	

    -- Create a fresh goal for the RHS constraints, i.e. for the D' derivation.
    setupC'Derivation state_c0@(State _ ucs_c0 _ _ extra_c0)
		      state_d'@(State _ ucs_d' _ _ extra_d') 
		      jrbcs jrucs fv_c0 fv_d' = do
	let (rucs,jrus) = unzip jrucs
	    (rbcs,jrbs) = unzip jrbcs
	
	-- Externalise the bcs to add to the bstore.
	rbs <- doHerbrand $ mapM (uncurry extOrigBCons) jrbcs

	-- Remove duplicates from variables
	global_vs <- doHerbrand $ keepVarsNoDeref (fv_c0 ++ fv_d')

	-- Generate initial goal from rucs, rbcs.
	goal_c@(State s u h i extra_c) <- doHerbrand $ createGoal (rucs ++ rbcs)
								  (jrus ++ jrbs)
					
        -- Combine this with the D' result.
	let extra_c' = extra_c { extraBStore = rbs ++ extraBStore extra_d' ++ 
					       extraBStore extra_c,
				 extraDelStore = extraDelStore extra_d',
				 extraVars = global_vs ++ extraVars extra_c,
				 extraTopVars = extraTopVars extra_d',
				 extraMatches = extraMatches extra_d',
				 extraLocInfo = extraLocInfo extra_d'  }
	    goal_c' = State (ustoreToStack ucs_d' ++ s) u h i extra_c'
	putState goal_c'

    -- Find C0 variables i.e. fv(C0), before any derivations are performed.
    findC0Vars state_c0@(State _ ucs_c0 _ _ extra_c0) = doHerbrand $ do
	vs_c0 <- findC0UconsVars ucs_c0
	keepVarsNoDeref (vs_c0 ++ extraVars extra_c0)

    -- Find significant variables, i.e. fv(C0,D,as) in D'.
    -- NOTE: Call this as soon as we have D', but before C' is calculated.
    findD'Vars state_c0@(State _ ucs_c0 _ _ extra_c0) 
	       state_d'@(State _ ucs_d' _ _ extra_d') evs_info = do
	
	vs_c0 <- doHerbrand $ do
			vs_c0 <- findC0UconsVars ucs_c0
			keepVarsNoDeref (vs_c0 ++ extraVars extra_c0)
	vs_d' <- doHerbrand $ keepVarsNoDeref (extraVars extra_d')
	vs_ex <- doHerbrand $ do
		tvs <- mapM extVarInfo evs_info
		let (evs, _) = unzip tvs
		keepVarsNoDeref evs

	return (vs_c0, vs_d', vs_ex)


    -- Extracts relevant information from the states to call the solved form
    -- check procedure.
    checkSolvedForm state_d'@(State _ ucs_d' _ _ extra_d')
                    state_c'@(State _ ucs_c' _ _ extra_c') 
		    (fv_c0, fv_d', fv_ex) = do
	
	-- Extract justified uc terms from states.
	let tjs_d' = map unwrapUStoreCons ucs_d'
	    tjs_c' = map unwrapUStoreCons ucs_c'

	-- Combine vars.
	let vs = nub (fv_c0 ++ fv_d' ++ fv_ex) 

{-
	cPut "------------ checkSolvedForm --------------- "
	cPut "vs:"
	mapM_ (cPut . show) vs
	cPut "dereferenced vs:"
	doHerbrand $ mapM_ printTerm vs
-}
	
	isSolvedForm vs tjs_d' tjs_c'


    -- At this point, we have processed a non-solved form implication, and
    -- extracted either a partial solution or recognised failure. 
    -- These cases are handled here.
    handlePotentialPartialSolution rewind state_c0 state_c' 
	orig_fv_c0 fvs_d'@(fv_c0,fv_d',fv_ex) j_ic sol = 
      case sol of
	
	-- Some universal variable instantiated.
	UnivInst t -> do  
	    cPut "UnivInst"
	    rewind
	    -- NOTE: We need to remove t from the list of *other* 
	    -- universal vars., or the error reporting may fail.
	    fv_ex' <- doHerbrand $ mapM extOrigType (delete t fv_ex)
	    v <- doHerbrand $ extOrigType t
	    let bcs      = getBStore state_c'
		fv_ex''  = map fromTVar fv_ex'
	    putState (FailedUniv bcs (fromTVar v) fv_ex'')
	    return CantSolve
		
		
	-- FIXME: we still want to associate the location information
	-- from the original variable names, with the current evs'.
	UnivEscaped t -> do
	    cPut "UnivEscaped"
	    rewind
	    fv_ex' <- doHerbrand $ mapM extOrigType fv_ex
	    let bcs     = getBStore state_c'
		fv_ex'' = map fromTVar fv_ex'
	    putState (FailedUnivEsc bcs t fv_ex'')
	    return CantSolve
      
      
        -- We have the new ucs and bcs.
        -- Undo the C',D' derivations, add the bcs and check if
        -- anything new was added (if not, and there are no ucs, 
        -- then fail - we can't solve this implication).
	ImpSoln new_ucs new_bcs -> do
	    cPut "ImpSoln"
{-	    
	    cPut ("new_bcs: " ++ pretty new_bcs)
	    let pr (t1,t2) = doHerbrand $ do
				printTerm t1 
				hPut " = " 
				printTerm t2
	    mapM_ pr new_bcs
-}
	    
	    -- NOTE: It's possible that the user constraints we lift out as 
	    -- part of the partial solution contain non-C0 variables which are 
	    -- ground, or instantiated by C0 variables. As soon as we rewind 
	    -- (to the point before either derivation) we will lose this 
	    -- connection. So, we need to build additional equations to 
	    -- represent these, and add them to the bcs returned.
	    uc_bcs <- doHerbrand $ uconsBindsToBCons new_ucs
	    let new_bcs' = uc_bcs ++ new_bcs
	    
	    -- Undo everything. We just need to check if the suggested new 
	    -- constraints add anything.
	    rewind
	    skol <- doHerbrand $ do
		    mapM_ (uncurry unify) new_bcs'   -- This can't fail.
		    canSkolemise orig_fv_c0
      
	    -- If skolemisation succeeded, then none of the C0
	    -- variables were grounded. Effectively, no new `real' 
	    -- herbrand constraints were suggested.
	    if skolOk skol && null new_ucs 
	      then do 
		-- Nothing new added, can't solve this implication.
		-- FIXME: ERROR REPORTING NOTE: This case should never arise!
		-- i.e. If the implication cannot be solved, we should detect
		-- it earlier, not here. At this point it is already
		-- assumed that the implication could be solved, it's just that
		-- we couldn't generate a meaningful partial solution.
		return CantSolve
	      else do
		-- Partially solved, return the user constraints.
		new_bcs'' <- pairsToBCons j_ic new_bcs'
		putState (addToBStore new_bcs'' state_c0)
		return (UpdatedStore new_ucs)


	-- Invoke the ImpSoln case.
	-- If it finds nothing was added via the bcs then fail.
	ImpSolnUnmatchedUCs ucs@((t,j):_) bcs -> do
	    cPut "ImpSolnUnmatchedUCs"
	    -- Extract a user constraint to potentially complain about before
	    -- calling the ImpSoln case, which will rewind the heap.
	    uc <- doHerbrand $ extUCons t j
	    let sol = ImpSoln [] bcs
	    res <- handlePotentialPartialSolution rewind state_c0 state_c' 
		    orig_fv_c0 fvs_d' j_ic sol
	    case res of
		-- Success: bcs are significant, forget about unmatched ucons.
		UpdatedStore {} -> return res
		
		CantSolve -> do
		    -- Failure case: bcs contribute nothing, report an unmatched
		    -- user constraint.
		    putState (FailedUCUnmatched uc)
		    return CantSolve


----------------------------------------

-- Given a list of terms (packaged in a UStore), representing a list of user 
-- constraints, returns a list of equations (as Term/Term pairs) mapping the
-- `immediate' type argument of each UC to its instantiated value. 
-- e.g. say the store contains: U t1 t2, t1 = t2, t2 = Int, 
--	we return (t1 = Int, t2 = Int)
uconsBindsToBCons :: UStore Term -> Herbrand Store [(Term,Term)]
uconsBindsToBCons store = do
    let ucs = map (fst . unwrapUStoreCons) store
    concatMapM binds ucs
  where
    binds :: Term -> Herbrand Store [(Term,Term)]
    binds uc = do
	(_,arr) <- functor uc
	ts <- mapM (arg uc) [1..arr]
	ts' <- mapM deref ts
	return (zip ts ts')

-- Converts a list of pairs of terms to justified built-ins. All equations
-- share the same justification.
pairsToBCons :: Just -> [(Term,Term)] -> CHRResult [BCons]
pairsToBCons j = doHerbrand . mapM mkBCons
  where
    mkBCons (t1,t2) = do
	t1' <- extOrigType t1
	t2' <- -- extType t2
	       extOrigType t2
	return ((t1' =+= t2') j)

--------------------------------------------------------------------------------
-- Procedures for finding a partial solution from an implication that is not in
-- solved form. 
-- NOTE: At this point, the Herbrand store implicitly represents the C' result.

-- Represents an attempt to solve an implication, cases include:
-- ImpSoln : new user constraints, and equations to add to the store
-- ImpSolnUnmatchedUCs: No user constraints could be lifted out into the
--	    partial solution; the ones we return are those which contained
--	    `bad' variables, either skolem, or non-C0. If it turns out that the
--	    equations add nothing, then we can report that these constraints
--	    remain unmatched.
-- UnivInst: a universal variable is already instantiated, can't continue
-- UnivEscaped: a universal variable t1, escapes (a C0 var, t2 is bound to it)
data ImpSoln = ImpSoln (UStore Term) [(Term,Term)]
	     | ImpSolnUnmatchedUCs [JTTerm] [(Term,Term)]
	     | UnivInst Term
	     | UnivEscaped Type

-- The current implication (being handled by solveImplication, above) is not a 
-- solved form (wrt current store), so extract some constraints from it to give
-- a partial solution, so we can continue. 
-- This is the Add step of the extended solver.
-- NOTE: The lists vs_c0 and evs contain terms that were still variables in the
--	 D' result. (They may no longer be variables if they were instantiated
--	 as part of the C' derivation.)
--
-- ERROR REPORTING NOTE: A number of things can go wrong at this point:
--  - Some user constraint on the RHS doesn't appear on the LHS
--    and can't be floated out.
--  - A universal variable is instantiated
--  - The top-level type variable is bound to a sk. constructor (univ. variable)
findPartialSolution :: JTTerm -> [Term] -> [Term] -> CHRState -> CHRState 
		    -> CHRResult ImpSoln
findPartialSolution (imp,j) vs_c0 evs 
		    state_d'@(State _ ucs_d' _ _ extra_d')
		    state_c'@(State _ ucs_c' _ _ extra_c') = do

{-
    cPut "--------------- evs ----------------"
    mapM_ (cPut . show) evs
    cPut "dereferenced evs:"
    doHerbrand $ mapM_ printTerm evs
-}
		    
    -- Skolemise the D' existential vars. (vars attached to the implication)
    cp   <- doHerbrand $ createCP
    skol <- doHerbrand $ skolemise evs
    if not (skolOk skol)
      then do 
	-- Skolemisation failed, some exist. var was instantiated in C'.
	-- ERROR REPORTING NOTE: Universal variable instantiated.
	rewind cp
	return (UnivInst (fromJust skol))
      else do

	-- ERROR REPORTING NOTE: We fail right away if the type bound to
	-- the top-level t variable contains a skolem constant. This 
	-- represents a polymorphic variable escaping from its scope. Even 
	-- if we weren't to fail immediately, we'd end up failing 
	-- eventually because the implication constraint will be found to 
	-- be unsolvable.
	esc <- findEscapees
	case esc of 
	  -- Top-level variable t has a type with a skolem constant bound to
	  -- it; this represents an escaping polymorphic variable.
	  (t:_) -> do
	    rewind cp
	    return (UnivEscaped t)
	    
	  -- No polymorphic variables escape.
	  [] -> do
	    -- Find equations on C0 vars implied by C'.
	    bcs_new <- findNewBCs 
	    -- Now look for user constraints in C' that were not in D'.
	    (ucs_soln, ucs_fail) <- findUnmatchedUCs
	    rewind cp

	    -- If there are no user constraints in the partial solution
	    -- (ucs_soln above), but there are unmatched constraints 
	    -- (ucs_fail from above) then return an ImpSolnUnmatchedUCs.)
	    return $ if null ucs_soln && not (null ucs_fail)
	      then ImpSolnUnmatchedUCs (map unwrapUStoreCons ucs_fail) bcs_new
	      else ImpSoln ucs_soln bcs_new
  where
    rewind :: ChoicePoint -> CHRResult ()
    rewind cp = doHerbrand $ rewindMaintainHeap cp

    -- Find any top-level type containing a skolem constant.
    findEscapees :: CHRResult [Type]
    findEscapees = do
	-- NOTE: We use extVar to extract the type and its embedded location 
	-- information (see Solvers.Convert's intVar and extVar.)
	-- We don't currently use the location info.
	tvs_top <- doHerbrand $ mapM extVar (extraTopVars extra_c')
	let (ts_top,vs_top) = unzip tvs_top
	    esc = [ t_top | t_top <- ts_top,
		    any (`hasPrefix`"SK!") (map nameStr (typeTCons t_top)) ]
	-- cPut ("tvs_top: " ++ pretty tvs_top)
	return esc

    -- Find equations on C0 vars implied by C'.
    findNewBCs :: CHRResult [(Term,Term)]
    findNewBCs = doHerbrand $ do
	-- Now find all equations representing the values of variables in 
	-- C0. These cannot contain any skolem consts, or non-C0 variables.
	ts_c0 <- termsToTypes vs_c0
	-- NOTE: This only works because extType also uses show to convert 
	-- vars. i.e. the `externalisation' is the same.
	vs_c0' <- mapM deref vs_c0
	let tvs_c0 = map show vs_c0'
	    vm = listToVarMap (zip (map mkVar tvs_c0) vs_c0')
	filterBCs vm (zip vs_c0 ts_c0)
	

    -- Find user constraints in C' that were not in D'. 
    -- Returns a tuple (ucs_soln, ucs_fail):
    -- ucs_soln: Can appear in solution; do not contain any skolem 
    --		 constants, (i.e. exist. vars) and variables are all in C0.
    --	   
    -- ucs_fail: Cannot appear in solution; contain `bad' variables, 
    --		 skolemised or non-C0.
    findUnmatchedUCs :: CHRResult (UStore Term, UStore Term)
    findUnmatchedUCs = doHerbrand $ do
	    -- Drop the C0Vars! user constraints before matching.
	    ucs_c' <- dropC0VarsUCons ucs_c'
	    ucs_d' <- dropC0VarsUCons ucs_d'
	    filterUCs ucs_c' ucs_d' [] []

    -- Given a variable mapping (from Haskell vars to terms), and a list of
    -- pairs representing the value of each C0 variable (as a Haskell type), 
    -- returns a list of pairs representing hebrand constraints binding each 
    -- (C) variable with its result.
    -- 
    -- The list of terms and types represents `candidate' equations.
    -- We filter out the equations where the C0 var. is mapped to a type
    -- containing either a non-C0 var.
    -- NOTE: We've already checked that none of the C0s is bound to anything
    -- containing a skolem constructor. (and failed, if that was the case)
    -- FIXME: add check for skolem cons!!
    filterBCs :: VarMap -> [(Term,Type)] -> Herbrand Store [(Term,Term)]
    filterBCs _  [] = return []
    filterBCs vm (tmt@(tm,t):tmts) = do
	let -- all variables must be in C0
	    all_c0 = all (`elemVarMap`vm) (fv t)
	    any_sk = any (`hasPrefix`"SK!") (map nameStr (typeTCons t))
	if  {-not all_c0 || -} any_sk
	  then -- dropped a candidate equation
	    filterBCs vm tmts
	  else do -- kept a candidate equation
	    (_, t') <- intType vm t
	    rest <- filterBCs vm tmts
	    return ((tm,t') : rest)

 
    -- Splits the user constraints from cs, which aren't in ds,
    -- into two groups:
    --  a) Those which can be lifted out as part of a partial solution.
    --	b) Those which contain variables which cannot be allowed to escape --
    --	   such a constraint represents an error.
    -- We can only lift out constraints that contain variables from C0, and no
    -- polymorphic variables.
    -- Note that if there are any constraints in the `b' group, we will
    -- immediately (upon returning from this function) fail.
    --
    -- ERROR REPORTING NOTE: User constraints already on the RHS are a-okay.
    -- Lifting out constraints which contain only C0 variables is okay too.
    -- Otherwise, we have the following cases:
    --	1) The uc contains a polymorphic variable.
    --  2) The uc contains a fresh variable (We ought to have a 
    --	   range-restrictedness check that would eliminate this.
    --	   But we don't do one yet.)
    -- We could handle these differently, but we don't. In both cases we just
    -- report that `some user constraint is unmatched'.
    --
    -- Some alternatives (corresponding to the cases above), include:
    --  1) Suggest adding a type class constraint to the relevant 
    --	   type declaration or data type guard. 
    --  2) Report this as an ambiguity error. i.e. tell the programmer where he
    --     can add type information to ground these fresh variables.
    filterUCs :: UStore Term -> UStore Term -> UStore Term -> UStore Term 
	      -> Herbrand Store (UStore Term, UStore Term)
    filterUCs []     ds as fs = return (as,fs)
    filterUCs (c:cs) ds as fs = do
	-- Check whether c is already in ds.
	copy <- let eq :: UStoreCons Term -> UStoreCons Term 
		       -> Herbrand Store Bool
		    eq t1 t2 = do let (t1',_) = unwrapUStoreCons t1
				      (t2',_) = unwrapUStoreCons t2
				  s <- eqeq t1' t2'
				  return (s == Success)
		in  anyM (eq c) ds
	
	-- This will be True if c should be eliminated because of its variables.
	-- These conditions are described below.
	badVs <- do let (uc,_) = unwrapUStoreCons c

		    -- Check if there are variables in uc, not appearing in C0.
		    vs_c0_deref <- mapM deref vs_c0
		    let vs_c0' = vs_c0_deref ++ vs_c0
		    vs <- fvCons uc
		    let new = any (`notElem`vs_c0') vs

		    -- Check if uc contains any existential vars
		    -- (which are skolemised at this point.)
		    as <- conArgs uc
		    -- let sk = any (`elem`dr_evs) dr_as
		    mts <- mapM findSkBound as

		    -- FIXME: This condition may be unnecessarily strong. e.g.
		    -- this user constraint could be in a nested implication,
		    -- but contains polymorphic variables from the outer
		    -- implication. (Could this even happen without an error?)
		    let sk = any isJust mts
		    
		    -- If either condition is True, c/uc is no good.
		    return (new || sk)

	let as' | copy || badVs = as
		| otherwise	= c:as
	    fs' | not copy && badVs = c:fs
		| otherwise	    = fs
	filterUCs cs ds as' fs'

--------------------------------------------------------------------------------

-- Find all the C0Vars! user constraints, and collect all their variables
-- (These are the free variables in C0.)
findC0UconsVars :: (Eq c, Herb s c) => UStore c -> Herbrand s [c]
findC0UconsVars ustore = do
    c0UCs <- hasC0Func ustore []
    vss   <- mapM getVars c0UCs
{-
    hPuts "c0UCs\n"
    mapM_ printTerm c0UCs
-}    
    return (concat vss)
  where
    -- Returns the terms representing the C0Vars! user constraints.
    hasC0Func [] ucs = return ucs
    hasC0Func ((Num (UCons f _ uc _) _):ss) ucs = do
	isC <- isCnst f
	if not isC then bug "findC0UconsVars: functor is not a constant!"
	  else do
	    cstr <- cnstName f
	    str  <- doIO $ peekCString cstr
	    let ucs' | str == "C0Vars!" = uc:ucs
		     | otherwise	= ucs
	    hasC0Func ss ucs'
    
    -- Returns all of the variables in one of these C0Vars! terms
    -- (it's a list of nested tuples in the term.)
    getVars uc = do
	t <- arg uc 1 
	vs <- fvType t
	return (nub vs)

-- Removes all the C0Vars! user constraints from the given store.
dropC0VarsUCons :: Herb s c => UStore c -> Herbrand s (UStore c)
dropC0VarsUCons us = do
    let ts = map (fst . unwrapUStoreCons) us
    fas <- mapM functor ts
    let fs = map fst fas
    fs' <- mapM (\f -> do nm <- cnstName f
			  doIO $ peekCString nm) fs
    return [ u | (f,u) <- zip fs' us, f /= "C0Vars!" ]

-- As above, but works directly on justified terms, rather than the UC store.
dropC0VarsJTerms :: Herb s c => [JTerm c] -> Herbrand s [JTerm c]
dropC0VarsJTerms ts = do
    fas <- mapM (functor . fst) ts
    let fs = map fst fas
    fs' <- mapM (\f -> do nm <- cnstName f
			  doIO $ peekCString nm) fs
    return [ u | (f,u) <- zip fs' ts, f /= "C0Vars!" ]
 
----------------------------------------

-- Keep only the terms which represent vars.
filterVars :: Herb s c => [c] -> Herbrand s [c]
filterVars ts = filt [] ts
      where
	filt vs [] = return vs
	filt vs (t:ts) = do 
	    isV <- isVar t
	    let vs' | isV = t:vs
		    | otherwise = vs
	    filt vs' ts

-- Like the above (filterVars), but also de-references the vars and removes
-- duplicates.
keepVars :: (Eq c, Herb s c) => [c] -> Herbrand s [c]
keepVars vs = do
    vs'  <- filterVars vs
    vs'' <- mapM deref vs'
    return (nub vs'')


keepVarsNoDeref :: (Eq c, Herb s c) => [c] -> Herbrand s [c]
keepVarsNoDeref vs = do
    vs'  <- filterVars vs
    vs'' <- mapM deref vs'

    let pvs = zip vs' vs''
	vs''' = map fst (nubBy eq pvs)
    
    return vs'''
  where
    eq (_,v1) (_,v2) = v1 == v2

nubVarsNoDeref :: (Eq c, Herb s c) => [c] -> Herbrand s [c]
nubVarsNoDeref vs = do
    vs' <- mapM deref vs

    let pvs = zip vs vs'
	vs'' = map fst (nubBy eq pvs)
    
    return vs''
  where
    eq (_,v1) (_,v2) = v1 == v2

----------------------------------------

-- Dereferences each term and converts the result into a Haskell type.
termsToTypes :: [Term] -> Herbrand Store [Type]
termsToTypes [] = return []
termsToTypes (tm:tms) = do
    tm' <- deref tm
    t   <- extType tm'
    ts  <- termsToTypes tms
    return (t:ts)

-- find a single sub-term which is bound to a skolem. cons
findSkBound :: Term -> Herbrand Store (Maybe Term)
findSkBound t0 = do
    t   <- deref t0
    isV <- isVar t
    if isV
      then return Nothing
      else do
        isC  <- isCnst t
        if isC 
          then do
            cstr <- cnstName t
            str  <- doIO $ peekCString cstr
            if str `hasPrefix` "SK!"
        	then return (Just t0)
        	else return Nothing
          else do -- ``It's an App!''
            t1 <- appArg t 0
            mb1 <- findSkBound t1
            case mb1 of 
              Just _  -> return mb1
              Nothing -> do
        	t2 <- appArg t 1
        	mb2 <- findSkBound t2
        	case mb2 of
        	  Just _  -> return mb2
        	  Nothing -> return Nothing


--------------------------------------------------------------------------------

-- Checks if the implication we just processed is a solved form wrt its context.
-- Takes a list of variables (fv(C_0,D_1,\bar{a})), a list of the
-- user constraints in the original D', and the user constraints in C'.
-- Note that the D' constraints are copies.
-- NOTE: Herbie skolemisation is broken by design - don't use it! 
--	 It sets all variables to the same skolem constant!
isSolvedForm :: [Term] -> [JTTerm] -> [JTTerm] -> CHRResult Bool
isSolvedForm vs ucs_d'0 ucs_c'0 = do
    cp  <- doHerbrand createCP
    -- First see if any LHS variables are affected.
    skol <- doHerbrand $ skolemise vs
    let eqsOkay = skolOk skol
    if not eqsOkay 
      then do -- They are, so it's not a solved form.
	-- cPut "isSolvedForm, variable instantiated"
	doHerbrand $ rewindMaintainHeap cp
	return False

      else do -- No variables affected, now check for matching ucons.
	-- Filter out the C0Vars! constraints.
	ucs_d' <- doHerbrand $ dropC0VarsJTerms ucs_d'0
	ucs_c' <- doHerbrand $ dropC0VarsJTerms ucs_c'0

	if null ucs_d' && null ucs_c' 
	  then return True  -- a trivial match (no user constraints present)
	  else do
	    -- Match `inferred' ucons. against `provided'.
	    -- First get LocInfo from out of the state, though.
	    st <- getState
	    let linfo = getLocInfo st
	    m <- doHerbrand $ matchUCons linfo ucs_c' ucs_d'
	    doHerbrand $ rewindMaintainHeap cp
	    case m of
		[] -> do -- No matching, not a solved form.
			 return False	

		_  -> -- A match, solved form!
		      do st <- getState
			 let linfo = getLocInfo st
			     ms = map (fromJust . Ev.buildMatch linfo) m
			 putState (addToMatches ms st)
			 return True	
  
-- Looks up the term associated with each variable in the VarMap.
lookupVars :: VarMap -> Herbrand Store [(Var,Type)]
lookupVars vm = do
	let vml = varMapToList vm
	    (vs, tms) = unzip vml
	ts <- mapM extType tms
	return (zip vs ts)

mkEq :: (Var,Type) -> BCons
mkEq (v,t) = (TVar v) =:= t

unwrapUStoreCons :: Herb s c => UStoreCons c -> (c, Just)
unwrapUStoreCons = \(Num (Solvers.CHRState.UCons _ _ t j) _) -> (t,j)

----------------------------------------

-- Skolemise terms, returns Nothing on success, Just t on failure, where t is
-- the term it failed to skolemise. 
-- NOTE: No skolemisation is undone, even in the case of failure.
skolemise :: [Term] -> Herbrand Store (Maybe Term)
skolemise = skolemiseConf True

-- As for skolemise, but always undoes all work before returning result.
canSkolemise :: [Term] -> Herbrand Store (Maybe Term)
canSkolemise = skolemiseConf False

-- Attempts to unify each term in the list with a new skolem constant.
-- If `go' is True, then the unification is performed, otherwise it is undone,
-- and the caller doesn't have to clean up anything.
-- NOTE: It's the caller's responsibility to not pass in any duplicates. (Which
--	 will involve dereferencing all the terms to check.)
skolemiseConf :: Bool -> [Term] -> Herbrand Store (Maybe Term)
skolemiseConf go ts =
    if go then skol ts
	  else do cp  <- createCP
		  res <- skol ts
		  rewind cp
		  return res
  where
    -- Returns Nothing if all terms are skolemised successfully, else Just the
    -- term that it failed on.
    skol [] = return Nothing
    skol (t:ts) = do
	sk <- genSkolemConst 
	stat <- unify t sk
	case stat of
	    Success -> skol ts
	    _ -> do return (Just t)

-- Tests whether skolemisation was successful.
skolOk :: Maybe a -> Bool
skolOk = isNothing

--------------------------------------------------------------------------------

-- Check whether there exists renaming function phi 
-- ( dom(phi) cap tvs = emptyset)
-- such that ucs2 = phi ucs1
-- Returns the matching (or an empty list, if there's no match).
--
-- This works by generating all possible pairs of constraints from the 
-- two lists, and eliminating those which aren't matchings.
-- Actually it's a bit cleverer in that it only generates potential matchings 
-- where the predicate symbols are the same.
-- 
-- Below, ucs1 are demanded/inferred ucs2 are declared/provided.
matchUCons :: LocInfo -> [JTTerm] -> [JTTerm] -> Herbrand Store [(Just, Just)]
matchUCons linfo jucs1 jucs2 = do 
    let ucs1 = map fst jucs1
	ucs2 = map fst jucs2

    -- Build all sensible combinations of pairs.
    jucs2_alts <- altMatch
    let ps = zip (repeat jucs1) jucs2_alts 
    -- Find a match.
    ms <- findMatch ps
    let m = case ms of
	      []	      -> [] -- No match.
	      ((ucs1,ucs2):_) -> 
		-- At least one match
		let js1 = map snd ucs1
		    js2 = map snd ucs2
		in  zip js1 js2    
    return m 
  where
  
    -- Goes through the list of potential matches, until it finds a real match,
    -- which it returns.
    findMatch :: [([JTTerm],[JTTerm])] -> Herbrand Store [([JTTerm],[JTTerm])]
    findMatch [] = return []
    findMatch (p:ps) = do m <- isMatch p
			  if m then return [p]
			       else findMatch ps

    -- True if the corresponding elements of each list match.
    isMatch :: ([JTTerm], [JTTerm]) -> Herbrand Store Bool
    isMatch (jucs1, jucs2) = do
	cp <- createCP
	ok <- checkMatches (zip jucs1 jucs2)
	rewind cp
	return ok
  
      where
	-- Check all individual constraint matches, stop as soon as 
	-- something fails.
	checkMatches :: [(JTTerm,JTTerm)] -> Herbrand Store Bool
	checkMatches [] = return True
	checkMatches (p:ps) = do
	    b <- checkMatch p
	    if b then checkMatches ps
		 else return False
      
	-- Checks whether a single pair of user constraints can be matched.
	-- There are two conditions to check: 
	-- 1) Justifications must be appropriate for code gen. (see below)
	-- 2) The predicates' types must be unifiable (note that universal
	--    variables will already have been skolemised.)
	checkMatch :: (JTTerm,JTTerm) -> Herbrand Store Bool
	checkMatch ((uc1,j1),(uc2,j2)) = do 
	    -- First check whether, if uc1 is strictly demanded, that uc2 is
	    -- strictly given. A strictly demanded constraint MUST be satisfied
	    -- by a strictly given constraint in order to build code for it.
	    if isDemanded j1
	      then if isGiven j2 
		     then -- demanded satisfied by given
			  logicalMatch
		     else -- demanded NOT satisfied by given: FAIL
			  return False
	      else -- uc1 not demanded, can match with anything
		   logicalMatch
	  where
	    isGiven = isJust . Ev.checkGiven linfo
	    isDemanded = isJust . Ev.checkDemanded linfo

	    logicalMatch = do
		stat <- unify uc1 uc2
		case stat of
		    Success -> return True
		    _	    -> return False
	  
  
    -- Generates all the potential matches.
    -- We should avoid generating obviously useless matches (i.e. where the
    -- predicate symbols are different.) So, first group each term in jucs2 by
    -- predicate symbol and get the symbols in jucs1 in order. Then
    -- generate all alternatives by walking down the jucs1 symbol list, only
    -- offerring as candidates those terms in the appropriate jucs2 group.
    altMatch :: Herbrand Store [[JTTerm]]
    altMatch = do
	-- Get all the predicate names.
	str1 <- mapM ucStr jucs1
	str2 <- mapM ucStr jucs2
	let ucs_str2 = zip str2 jucs2
	    -- Group all the constraints in jucs2 by name.
	    group = foldr addToGroup [] ucs_str2
	    alts  = map (find group) str1
	    -- Generate all the potential matches.
	    cs = combos alts
	return cs
      where
	-- Returns the predicate name.
	ucStr (uc,j) = do (f,_) <- functor uc
			  cstr  <- cnstName f
		          doIO (peekCString cstr)
  
	-- Given the list of jucs2 groups matched against jucs1 predicate
	-- symbols, generates all potential matches.
	combos :: [[JTTerm]] -> [[JTTerm]]
	combos [] = [[]]
	combos (ts:tss) = let cs = combos tss
			  in  [ t:c | t <- ts, c <- cs ]
  
	-- NOTE: If we hit the Nothing case below, the whole matchUCons
	--	 procedure will end up failing. We should fail asap.
	find :: [(String, [JTTerm])] -> String -> [JTTerm]
	find g str = case List.lookup str g of
			Nothing -> []
			Just ps -> ps
  
	-- Builds up the grouping of constraints by predicate symbol.
	addToGroup :: (String, JTTerm) -> [(String, [JTTerm])]
		   -> [(String, [JTTerm])]
	addToGroup (str, t) g = 
	    let (a,b) = span ((/=str) . fst) g
	    in  case b of
		    [] -> (str,[t]) : a
		    ((s',ts):xs) -> (s',t:ts) : xs ++ a
  
----------------------------------------

printUStore ucs = do
    let ts = map (fst . unwrapUStoreCons) ucs
    doHerbrand $ mapM_ printTerm ts

printVars :: [Term] -> Herbrand Store ()
printVars = mapM_ print 
  where
    print t = do 
	-- printTerm_ t
	doIO $ putStrLn (show t ++ " = ")
	printTerm t
	doIO $ putStr "\n"


-- Like `rewind', but does not rewind heap usage.
rewindMaintainHeap :: Herb s c => CInt -> Herbrand s ()
rewindMaintainHeap cp = do
    setFlag NoRewindHeap On
    rewind cp
    setFlag NoRewindHeap Off


--------------------------------------------------------------------------------
--

-- Runs the given CHR rules on each inference goal, resulting in a list of
-- list of inference results.
-- This works by: a) creating a new store, b) compiling all the CHRs in
-- that store, c) solving all goals in that same store, rewinding after each.
-- NOTE: simply calls runInfGoalsLocInfo with an emptyLocInfo
runInfGoals :: [Core.CHR.CHR] -> [InfGoal] -> IO [InfResult]
runInfGoals = runInfGoalsLocInfo emptyLocInfo

runInfGoalsLocInfo :: LocInfo -> [Core.CHR.CHR] -> [InfGoal] -> IO [InfResult]
runInfGoalsLocInfo linfo chrs0 igs = do
    
    putStrLn "runInfGoalsLocInfo"

    let chrs = propsFirst chrs0
    -- create a new store to do all this in
    st  <- newStore
    -- and a new VarMap (maps Haskell-side variables to Herbie terms)
    irs <- runHerbrand st (runCHRInit (do
	    -- we split the CHRs into two groups: 
	    --  - the HMRules (H/M inference rules)
	    --  - the rest
	    -- All CHR derivations will be staged so that the H/M rules are
	    -- always applied first.
	    let (hm_chrs, other_chrs) = partition isHMRule chrs

	    ichrss <- mapM (mapM (doHerbrand . intCHR emptyVarMap))
			   [hm_chrs,other_chrs]
	    progs  <- doHerbrand $ mapM compileCHRsNoReorder ichrss

	    -- Solve all the goals.
	    solveAll progs igs ))
	
    -- delete the store - we're done with it
    deleteStore st
    return irs

  where

    -- We keep track of the id's of goals which have failed. If one goal has
    -- failed, we don't run any subsequent goals for that id.
    solveAll :: Progs Term -> [InfGoal]
	     -> CHRResult [InfResult]
--    solveAll progs igs = thread Set.emptySet igs []
    solveAll progs igs = thread Set.empty igs []
      where
	thread _  []       rs = return rs
	thread fs (ig:igs) rs 
--	  | infId ig `Set.elementOf` fs = thread fs igs rs
	  | infId ig `Set.member` fs = thread fs igs rs
	  | otherwise = do
	    r <- solve emptyVarMap progs ig
	    -- if it was a failure, add the id to the fail set
--	    let fs' | isFailure r = Set.addToSet fs (infId ig)
	    let fs' | isFailure r = (flip Set.insert) fs (infId ig)
		    | otherwise	  = fs
	    thread fs' igs (r:rs)

  
    -- The procedure for solving a single goal.
    solve :: VarMap -> Progs Term -> InfGoal 
	  -> CHRResult InfResult
    solve vm0 progs ig = do
	-- create a choice point
	cp <- doHerbrand createCP
	-- internalise the goal constraints
	(vm1, itjs) <- doHerbrand $ intConstraint vm0 (infCons ig)
	
	-- Internalise the t component (the only top-level var.), and embed the
	-- relevant source information (in case of an error.) Actually, `t' is
	-- already internalised, so intVar will just retrieve it and tag it
	-- with the extra info.
	-- NOTE: If this is a subsumption goal, do NOT store any top-level
	-- variable (since it will always be unified with the declared type and
	-- thereby trivially allow variable escape -- even though they're not
	-- existential variables!)
	t0s <- if isSubGoal ig then return []
	       else do
		let (t:_) = infTLV ig 
		(_, t0) <- doHerbrand $ intVar vm1 t
		return [t0]
		
	-- solve, and then extract the result from the final state
	setupInitialState linfo t0s progs itjs
	extendedSolver progs
	state <- getState
	(ucs0,ics) <- doHerbrand $ getCons state

	-- get rid of the C0Vars! user constraints
	let ucs = filter ((/="C0Vars!") . nameStr . ucName) ucs0
	-- look up the value of each of the original vars., and
	-- generate a corresponding equation.
	vts <- doHerbrand $ lookupVars vm1
	let id   = infId  ig
	    tlv  = infTLV ig
	    ttlv = map TVar tlv
	    tlv' = [ t | v <- tlv, (v',t) <- vts, v == v' ]
	    bcs  = map mkEq vts
	    cons = ics /\ ucs /\ bcs
	    cons' = cons /\ getBStore state
	    res = case state of 
		Failed   {} -> InfFailure id cons'

		FailedBS {} -> InfFailure id cons'
		
		FailedUniv _ v vs -> 
		    let v' = originalVar vm1 v
		    in  InfFailureUniv id v' vs cons'
				     
		FailedUnivEsc _ t vs -> 
		    let vs' = map (originalVar vm1) vs
		    in  InfFailureUnivEsc id (fromTVar (head ttlv)) t vs' cons'
				       
		FailedUCUnmatched uc -> InfFailureUConsUnmatched id uc

		State {} | isSubGoal ig -> SubSuccess id
			 | otherwise    -> InfSuccess id tlv' cons
	
	-- rewind to the choice point
	doHerbrand $ rewind cp
	return res

--------------------------------------------------------------------------------
-- TEST CASES

solve :: Constraint -> IO ()
solve c = do 
    (rs, _, _) <- solveTypingConstraint [] [] [] [] emptyLocInfo c
    print (all isInfSuccess rs)


c2 = toConstraint (ic vs k1 k2)
  where
    vs = map fromTVar [v 'a']
    k1 = [v 't' =:= (erk (v 'a') `arrow` v 'a')]
    k2 = toConstraint (v 't' =:= (v 'p' `arrow` v 'r'), imp)
      where
	imp = ic [] k1 k2
	k1 = [v 'a' =:= int]
	k2 = [v 'p' =:= erk (v 'x'), v 'r' =:= int]
	  
    erk t = tc "Erk" `ap` t
    int = tc "Int"


c1 = toConstraint (bcs,ucs,ics)
  where
    bcs = [v 1 =:= v 2, 
	   tc "T" =:= tc "S"]
    ucs = [] :: [Core.Constraint.UCons]
    ics = [] :: [ICons]
 
v :: Show a => a -> Core.Types.Type   
v = vr . show
vr = Core.Types.TVar . Core.Types.mkVar
tc = Core.Types.TCon . mkFreeName
ap = Core.Types.TApp
arrow t1 t2 = ((tc "->") `ap` t1) `ap` t2
ic vs c1 c2 = IC vs l r noJust
  where
    l = (cUCons c1', cBCons c1')
    r = (cUCons c2', cBCons c2', cICons c2')
    c1' = toConstraint c1
    c2' = toConstraint c2


--------------------------------------------------------------------------------
-- OLD STUFF



{-
cPuts :: String -> CHRResult ()
cPuts = const (return ())
	-- doHerbrand . doIO . putStrLn

cPuts' :: String -> CHRResult ()
cPuts' = doHerbrand . doIO . putStrLn

hPuts :: Herb s c => String -> Herbrand s ()
hPuts = doIO . putStrLn
	-- const (return ())


hPuts2 :: String -> Herbrand Store ()
hPuts2 = doIO . putStrLn

printTerm_ = const (return ())
	     -- printTerm 
-}

