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
-- Implementor: J. Wazny
-- Maintainer : J. Wazny
--------------------------------------------------------------------------------
--
-- Converts types, constraints, CHR rules from the format known to the rest of
-- the system (the external format) to the format understood by this solver
-- (the `internal' format.) We call this "internalisation."
-- 
-- Also does the reverse process, aka "externalisation."
--
-- NOTE: Throughout this module we limit ourselves to Herbie terms, when, to
--	 be more general we should allow any terms which are in the Herbrand
--	 class.
--
-- NOTE: I've tried using a HashTable for VarMaps, but the performance is
--	 far, far worse than for FiniteMaps (by a factor of 10-1000.) This is
--	 pretty weird. 
--
-- NOTE: Before switching to FiniteMap, we used a list, and it turned out that 
--	 for anything but tiny programs, `intType' was the bottleneck.
--	 With VarMaps as lists, the running time seemed exponential in the
--	 program size. (double the size -> 100 times longer). Running time is
--	 now about linear. (This is for extremely simple programs without
--	 recursion, or deep function or callgraph nesting.)
--	 
--------------------------------------------------------------------------------

-- NOTE: tighten up this export list a bit.
module Solvers.Convert (
    module Solvers.Convert,  module I, 
    module Solvers.Herbrand, module Solvers.HsHerbie, module Solvers.Misc
)
where

import IO
import Monad
import List
import Foreign.C
import Foreign.C.String

-- import Data.FiniteMap
import Data.Map
-- import qualified Data.HashTable as HT

import Solvers.Misc
-- import qualified Solvers.CHR as I
import qualified Solvers.CHRRule    as I
import qualified Core.CHR	    as E
import qualified Solvers.CHRState   as S
import Solvers.Herbrand
import Solvers.HsHerbie
import Core.Types
import Core.Constraint
import Core.Justify
import Core.Name
import Core.CHRGenerator
import Misc

import qualified Solvers.CHRState   as I

--------------------------------------------------------------------------------

-- a `justified' term
type JTerm c = (c, Just)

----------------------------------------

-- A mapping from external variables to Herbie terms
-- NOTE: in general these should be any terms which are members of Herbrand
-- type VarMap = FiniteMap Var Term
type VarMap = Map Var Term

emptyVarMap :: VarMap
-- emptyVarMap = emptyFM
emptyVarMap = empty

varMapToList :: VarMap -> [(Var,Term)]
-- varMapToList = fmToList
varMapToList = toList

varMapTerms :: VarMap -> [Term]
-- varMapTerms = map snd . fmToList 
varMapTerms = List.map snd . toList 

listToVarMap :: [(Var,Term)] -> VarMap
-- listToVarMap = listToFM
listToVarMap = fromList

elemVarMap :: Var -> VarMap -> Bool
-- elemVarMap = elemFM
elemVarMap = member

lookupVarMap :: Var -> VarMap -> Maybe Term
-- lookupVarMap v vm = lookupFM vm v
lookupVarMap v vm = Data.Map.lookup v vm

-- reverse VarMap: maps terms which are vars to types
type RevVarMap = [(Var,Type)]

mkRevVarMap :: VarMap -> Herbrand Store RevVarMap
mkRevVarMap vm = concatMapM rev (varMapToList vm)
  where
    rev (v,tm) = do
	t <- extType tm
	if isTVar t 
	  then return [(fromTVar t, TVar v)]
	  else return []

----------------------------------------

-- Given a variable v, finds the variable mapped to v by the VarMap
-- NOTE: This is too inefficient to use often.
originalVar :: VarMap -> Var -> Var
originalVar vm v0 = lookup (varMapToList vm)
  where
    v = varNameStr v0
    lookup [] = v0
    lookup ((v1,v2):vvs) | show v2 == v = v1
			 | otherwise    = lookup vvs

----------------------------------------
-- internalise types

-- NOTE: all information in type variables is lost (e.g. source location)

intType :: VarMap -> Type -> Herbrand Store (VarMap, Term)
intType vm (TVar v) = -- case lookupFM vm v of
                      case Data.Map.lookup v vm of
			Nothing -> do tm <- var
--				      let vm' = addToFM vm v tm
				      let vm' = Data.Map.insert v tm vm
				      return (vm', tm)
			Just tm -> return (vm, tm)

intType vm (TCon c) = do 
    cstr <- doIO $ newCString (nameStr c)
    ct   <- cnst cstr
    return (vm, ct)

intType vm (TApp t1 t2) = do 
    (vm1, tm1) <- intType vm  t1
    (vm2, tm2) <- intType vm1 t2
    tm3 <- app tm1 tm2
    return (vm2, tm3)

----------------------------------------
-- Internalise a variable, retaining all source information. 
-- We use the same trick to embed variable information as we do for
-- justifications. (Namely, to represent it as a string and turn it into a term
-- constructor.)

-- We want to do this for polymorphic variables in an implication, so that we
-- can get back the necessary source information if there's a type error.
intVar :: VarMap -> Var -> Herbrand Store (VarMap, Term)
intVar vm v = do
    (vm',t) <- intType vm (TVar v)
    info <- doIO $ newCString (show v)
    nm <- doIO $ newCString "Var"
    c  <- cnst nm
    i  <- cnst info
    tm <- construct c [t,i]
    return (vm', tm)

----------------------------------------
-- internalise constraints
--

intUCons :: VarMap -> UCons -> Herbrand Store (VarMap, (Term,Just))
intUCons vm (UC nm ts j) = do
    cstr <- doIO $ newCString (nameStr nm)
    c    <- cnst cstr
    (vm',ts') <- thread intType vm ts
    tm <- construct c ts'
    return (vm',(tm,j))

-- Note: we end up recreating this same "=" string for each constraint
intBCons :: VarMap -> BCons -> Herbrand Store (VarMap, (Term,Just))
intBCons vm bc@(Eq t1 t2 j) = do
   cstr <- doIO $ newCString "="
   eq   <- cnst cstr
   (vm1,tm1) <- intType vm  t1
   (vm2,tm2) <- intType vm1 t2
   tm <- construct eq [tm1,tm2]
   return (vm2,(tm,j))

pairToBCons :: (Term, Term) -> Herbrand Store Term
pairToBCons (tm1, tm2) = do
    cstr <- doIO $ newCString "="
    eq   <- cnst cstr
    construct eq [tm1,tm2]
    
-- We create a term (which looks like a user constraint to Herbie) with the 
-- following information embedded: 
--  - universally quantified/polymorphic variables 
--  - LHS constraints (justified)
--  - RHS constraints (justified)
intICons :: VarMap -> ICons -> Herbrand Store (VarMap, (Term, Just))
intICons vm ic@(IC vs (lucs,lbcs) (rucs,rbcs,rics) j) = do
    (vm1, lutj) <- thread intUCons vm  lucs
    (vm2, lbtj) <- thread intBCons vm1 lbcs
    (vm3, rutj) <- thread intUCons vm2 rucs
    (vm4, rbtj) <- thread intBCons vm3 rbcs
    (vm5, ritj) <- thread intICons vm4 rics
    (vm6, vs')  <- thread intVar vm5 vs
 
    -- Simply add the implications in with the user constraints; the solver
    -- will recognise and separate them all out eventually anyway.
    rutj <- return (rutj ++ ritj)
 
    lucs' <- mapM mkJustTerm lutj
    lbcs' <- mapM mkJustTerm lbtj
    rucs' <- mapM mkJustTerm rutj
    rbcs' <- mapM mkJustTerm rbtj
   
    -- implication var. constructor
    cstr  <- doIO (newCString "VS!")
    varsC <- cnst cstr
    vars  <- construct varsC vs'
    -- implication lhs constructor
    cstr <- doIO (newCString "LHS!")
    lhsC <- cnst cstr
    lhs  <- construct lhsC (lucs'++lbcs')
    -- implication lhs constructor
    cstr <- doIO (newCString "RHS!")
    rhsC <- cnst cstr
    rhs  <- construct rhsC (rucs'++rbcs')
    -- implication constructor
    cstr <- doIO (newCString "IMP!")
    impC <- cnst cstr
    imp  <- construct impC [vars, lhs, rhs]
    
    return (vm5, (imp, j))
 
  where
    -- builds a Term with a justification; result is of form (term @ j) 
    -- NOTE: we encode justifications as constants whose string name is the
    --	     justification (we use show/read to encode and decode this)
    mkJustTerm :: (Term, Just) -> Herbrand Store Term
    mkJustTerm (t,j) = do
	cstr <- doIO (newCString (show j))
	jC   <- cnst cstr
	app t jC
 
-- NOTE: the terms appear in the list in the same order as in the original
-- constraint; (including ucs before bcs)
intConstraint :: VarMap -> Constraint -> Herbrand Store (VarMap, [(Term,Just)])
intConstraint vm c = do
    (vm1, tm_ucs) <- thread intUCons vm  (cUCons c)
    (vm2, tm_bcs) <- thread intBCons vm1 (cBCons c)
    (vm3, tm_ics) <- thread intICons vm2 (cICons c)
    return (vm3, tm_ics ++ tm_ucs ++ tm_bcs)

----------------------------------------
-- internalise CHR rules

intCHR :: VarMap -> E.CHR -> Herbrand Store (I.Rule Term)
intCHR vm r = case r of
    E.SimpRule _ ucs c -> int I.SimpRule (ucs,c)
    E.PropRule _ ucs c -> int I.PropRule (ucs,c)
  where
    int mkRule (ucs,c) = do
	(vm1, tmj_ucs) <- thread intUCons vm ucs
	(vm2, tmj_cs)  <- intConstraint vm1 c
	let (tm_ucs,_) = unzip tmj_ucs
	    (tm_cs,js) = unzip tmj_cs
	return (mkRule tm_ucs tm_cs js)


--------------------------------------------------------------------------------
-- externalisation 

-- Externalises a term representing a type. Will optionally dereference
-- variables if flag dr is True.
-- NOTE: This should only be called for terms which actually represent types.
--       (which can only appear within constraints.)
extTypeConf :: Herb s c => Bool -> c -> Herbrand s Type
extTypeConf dr t0 = do
    t <- if dr then deref t0 else return t0
    isV <- if dr then isVar t else wasVar t
    if isV then return (TVar (mkVar (show t)))
     else do
      isC <- isCnst t
      if isC then do
	cstr <- cnstName t
	str  <- doIO $ peekCString cstr
	return (TCon (mkFreeName str))
       else do
	-- Admiral Ackbar sez: It's an app!
	tm_l <- appArg t 0
	tm_r <- appArg t 1
	l <- ext tm_l
	r <- ext tm_r
	return (TApp l r)
  where
    ext = extTypeConf dr

extType :: Herb s c => c -> Herbrand s Type
extType = extTypeConf True

extOrigType :: Herb s c => c -> Herbrand s Type
extOrigType = extTypeConf False

-- externalises a type, but uses the given var. map to name variables.
extTypeViaVarMap :: VarMap -> Term -> Herbrand Store Type
extTypeViaVarMap vm tm = ext tm
  where
    vm_list = varMapToList vm
    lookup v [] = mkVar (pretty v)
    lookup v ((v1,v2):vvs) | v2 == v   = v1
			   | otherwise = lookup v vvs

    ext tm = do
	t <- deref tm
	isV <- isVar t
	if isV then return (TVar (lookup t vm_list))
	 else do
	  isC <- isCnst t
	  if isC then do
	    cstr <- cnstName t
	    str  <- doIO $ peekCString cstr
	    return (TCon (mkFreeName str))
	   else do
	    -- Admiral Ackbar sez: It's an app!
	    tm_l <- appArg t 0
	    tm_r <- appArg t 1
	    l <- ext tm_l
	    r <- ext tm_r
	    return (TApp l r)

----------------------------------------

-- Externalise a Var with embedded source information.
-- The first return value is the name of the type as it appears in the store,
-- the second is the original Var.
extVar :: Herb s c => c -> Herbrand s (Type, Var)
extVar t = do
    a1 <- arg t 1
    a2 <- arg t 2
    t  <- extType a1
    cstr <- cnstName a2
    str  <- doIO $ peekCString cstr
    return (t, read str)

-- pulls apart a term representing an embedded (with info), and returns the var
-- term and info components
extVarInfo :: Herb s c => c -> Herbrand s (c, Var)
extVarInfo t = do
    a1 <- arg t 1
    a2 <- arg t 2
    cstr <- cnstName a2
    str  <- doIO $ peekCString cstr
    return (a1, read str)



-- NOTE: Only call this for terms which actually represent user constraints!
--       (which by construction can only appear within the UStore)
extUCons :: Term -> Just -> Herbrand Store UCons
extUCons tm j = do
    (func, arity) <- functor tm
    isC <- isCnst func
    when (not isC) (bug "extUCons: functor is not a constant!")
    cstr <- cnstName func
    str  <- doIO (peekCString cstr)
    ts   <- extArgs arity []
    let nm = mkFreeName str
	uc = UC nm ts j
    return uc

  where
    extArgs 0 ts = return ts
    extArgs n ts = do a <- arg tm n
		      t <- extType a
		      extArgs (n-1) (t:ts)

-- Converts a term into a herbrand constraint.
-- NOTE: does not perform any checking of the term, hence may crash if the term
--	 really doesn't represent a herbrand constraint!
extBCons :: Herb s c => c -> Just -> Herbrand s BCons
extBCons tm j = do 
    tm1 <- arg tm 1
    tm2 <- arg tm 2
    t1  <- extType tm1
    t2  <- extType tm2
    return (Eq t1 t2 j)

-- As above, but does not dereference variables when externalising types.
extOrigBCons :: Herb s c => c -> Just -> Herbrand s BCons
extOrigBCons tm j = do
    tm1 <- arg tm 1
    tm2 <- arg tm 2
    t1  <- extOrigType tm1
    t2  <- extOrigType tm2
    return (Eq t1 t2 j)


-- Converts a term representing an implication into a real implication.
-- NOTE: does not perform any checking of the term, hence may crash if the term
--	 really doesn't represent an implication!
extICons :: Term -> Just -> Herbrand Store ICons
extICons tm j = do
    (vs,lucs,lbcs,rucs,rbcs) <- disectICons tm
    tvs <- mapM extVar vs
    lucs' <- mapM (uncurry extUCons) lucs
    lbcs' <- mapM (uncurry extBCons) lbcs
    rucs' <- mapM (uncurry extUCons) rucs
    rbcs' <- mapM (uncurry extBCons) rbcs
    let vs' = List.map snd tvs
    return (IC vs' (lucs',lbcs') (rucs',rbcs',[]) j)

-- Takes a term representing an implication, and breaks it into its five
-- components (in order): 
--  1. universal variables
--  2. lhs user constraints
--  3. lhs herbrand constraints
--  4. rhs user constraints
--  5. rhs herbrand constraints
-- NOTE: Must pass in a well-formed implication term!
disectICons :: Herb s c => c
	    -> Herbrand s ([c], [JTerm c], [JTerm c], [JTerm c], [JTerm c])
disectICons tm = do
    tm1 <- arg tm 1
    tm2 <- arg tm 2
    tm3 <- arg tm 3
    vs  <- toList tm1
    lhs <- toList tm2
    rhs <- toList tm3
    (lucs,lbcs) <- split lhs
    (rucs,rbcs) <- split rhs
    lucs' <- mkJTerms lucs
    lbcs' <- mkJTerms lbcs
    rucs' <- mkJTerms rucs
    rbcs' <- mkJTerms rbcs
    return (vs,lucs',lbcs',rucs',rbcs')
  where

    mkJTerms = mapM mkJTerm

    -- turns a single justified term into a JTerm
    mkJTerm :: Herb s c => c -> Herbrand s (JTerm c)
    mkJTerm tj = do
	t <- appArg tj 0
	j <- appArg tj 1
	cstr <- cnstName j
	str  <- doIO (peekCString cstr)
	return (t, read str)
  
    -- splits terms into user and built-in constraints
    -- NOTE: split is processing `justified' terms
    split :: Herb s c => [c] -> Herbrand s ([c], [c])
    split []       = return ([],[])
    split (tj:tjs) = do
	(us,bs) <- split tjs
	t   <- arg tj 0
	isB <- isBCons t
	return $ if isB then (us,tj:bs)
			else (tj:us,bs)

    toList :: Herb s c => c -> Herbrand s [c]
    toList tm = do
	(ftr,arity) <- functor tm
	getArgs arity []
      where
	getArgs 0 ts = return ts
	getArgs n ts = do t <- arg tm n
			  getArgs (n-1) (t:ts)


--------------------------------------------------------------------------------

isFailedState :: I.State c -> Bool
-- isFailedState NorthKorea = True
isFailedState (I.State {})  = False
isFailedState _ = True

mkFailedState :: I.State c -> I.State c
mkFailedState (I.State _ _ _ _ x) = I.FailedBS (S.extraBStore x)
mkFailedState st = st
 
-- Given the CHR state, extracts all user and implication constraints from the
-- user constraint store.
-- getCons :: I.State Term -> Herbrand Store ([UCons],[ICons])
getCons state = do 
    (uts,its) <- splitUConsICons state
    let uts' = List.map unwrap uts
	its' = List.map unwrap its
    ucs <- mapM (uncurry extUCons) uts'
    ics <- mapM (uncurry extICons) its'
    return (ucs,ics)
  where
    unwrap = \(I.Num (I.UCons _ _ t j) _) -> (t,j)

-- splits all the terms in the user store of the state into user and
-- implication constraint terms
splitUConsICons :: Herb s c => I.State c 
		-> Herbrand s ([I.UStoreCons c], [I.UStoreCons c])
splitUConsICons st = case st of
    I.State _ ts _ _ _ -> do
	es <- mapM split ts
	return (splitEither es)

    _ -> return ([],[])
	
  where
    split c@(I.Num (I.UCons func arity term j) _) = do
	isImp <- isICons term
	return $ if isImp then Right c
			  else Left  c

getBStore :: I.State c -> [BCons]
getBStore I.Failed    = []
getBStore I.FailedImp = []
getBStore I.FailedUCUnmatched {} = []
getBStore (I.FailedBS bstore)	       = bstore
getBStore (I.FailedUniv bstore _ _)    = bstore
getBStore (I.FailedUnivEsc bstore _ _) = bstore
getBStore (I.State _ _ _ _ x) = S.extraBStore x


setBStore :: [BCons] -> I.State c -> I.State c
setBStore bstore st = case st of
    I.FailedBS _ -> I.FailedBS bstore
    I.FailedUniv _  v vs -> I.FailedUniv bstore v vs
    I.FailedUnivEsc _ t vs -> I.FailedUnivEsc bstore t vs
    I.State s u h d x -> I.State s u h d (x {S.extraBStore = bstore})
    _ -> st

addToBStore :: [BCons] -> I.State c -> I.State c
addToBStore bcs st = case st of 
    I.FailedBS bstore -> I.FailedBS (bcs ++ bstore)
    I.FailedUniv bstore v vs -> I.FailedUniv (bcs ++ bstore) v vs
    I.FailedUnivEsc bstore v vs -> I.FailedUnivEsc (bcs ++ bstore) v vs
    I.State s u h d x -> 
	    I.State s u h d (x { S.extraBStore = bcs ++ S.extraBStore x })
    st -> st

addToMatches :: Matches -> I.State c -> I.State c
addToMatches ms (I.State s u h d x) =
		I.State s u h d (x { S.extraMatches = ms ++ S.extraMatches x })
addToMatches _ st = st

getMatches :: I.State c -> Matches
getMatches (I.State _ _ _ _ x) = S.extraMatches x
getMatches _ = []

getLocInfo :: I.State c -> LocInfo
getLocInfo (I.State _ _ _ _ x) = S.extraLocInfo x
getLocInfo _ = emptyLocInfo

setLocInfo :: LocInfo -> I.State c -> I.State c
setLocInfo li (I.State s u h d x) = 
		I.State s u h d (x { S.extraLocInfo = li })

getTopVars :: I.State c -> I.Vars c
getTopVars (I.State _ _ _ _ x) = S.extraTopVars x
getTopVars _ = []

setTopVars :: I.Vars c -> I.State c -> I.State c
setTopVars tvs (I.State s u h d x) = 
		I.State s u h d (x { S.extraTopVars = tvs })

getStateExtra :: I.State c -> I.ExtraState c
getStateExtra (I.State _ _ _ _ x) = x

--------------------------------------------------------------------------------

ustoreToStack :: Herb s c => S.UStore c -> S.Stack c
ustoreToStack = List.map (S.UserCons . (\(S.Num uc _) -> uc))
        
stackToUStore :: Herb s c => S.Stack c -> S.UStore c
stackToUStore ss = let ucs = concatMap (\s -> case s of
                                            S.UserCons c -> [c]
                                            _ -> []) ss
                   in  List.map (flip S.Num (-99)) ucs
        
