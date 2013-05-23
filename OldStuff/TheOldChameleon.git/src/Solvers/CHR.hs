--------------------------------------------------------------------------------
-- CHR.hs -- A CHR interpreter for GHC
--   Copright (C) 2004 Gregory J. Duck
--   (Modified/Improved by The Chameleon Team)
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

module Solvers.CHR (
    Rule(SimpRule,PropRule), 
    derivationStep, derivation, stagedDerivation,
    compileCHRsNoReorder, compileCHRs, createGoal
) where

--------------------------------------------------------------------------------

import List
import Maybe
import Monad
import Foreign.C
-- import Data.FiniteMap
import Data.Map

import Misc
import Solvers.Herbrand
import Solvers.CHRState
import Solvers.CHRRule
import Solvers.Convert
import Solvers.Misc
import Core.Justify

import Debug.Trace

--------------------------------------------------------------------------------

-- a deleted user constraint, flag indicates whether it should be replaced by
-- an equation or not
type DelUCons c = (UCons c, Bool)

derivationStep :: Herb s c => Prog c -> CHR s c ()
derivationStep prog = do
    state <- getState
    unless (isFinalState state) $ do
         newstate <- doHerbrand (transition prog state)
         putState newstate
    

-- Performs a sequence of derivations, on the same store, using the each given
-- program in turn. NOTE: once a program is applied, we don't return to it!
-- There should be no backward dependencies amongst the programs. i.e. it
-- should never be the case that a constraint introduced by a latter program
-- could cause a rule in an earlier program to fire.
stagedDerivation :: Herb s c => Progs c -> CHR s c ()
stagedDerivation ps = mapM_ step ps
  where
    -- Before each stage/step we need to take the user constraints from the 
    -- store and place them back on the stack.
    step :: Herb s c => Prog c -> CHR s c ()
    step p = do
	state <- getState
	if isFailedState state 
	  then return ()
	  else do 
	    let State s u h id x = state
		state' = State (ustoreToStack u ++ s) [] h id x
	    putState state'
	    derivation p
	

derivation :: Herb s c => Prog c -> CHR s c ()
derivation prog = do
    state <- getState
    final <- doHerbrand (derivation' prog state)
    putState final

derivation' :: Herb s c => Prog c -> State c -> Herbrand s (State c)
derivation' prog state = do
    if isFinalState state
      then do
        return state
      else do
        nextstate <- transition prog state
        derivation' prog nextstate

isFinalState :: State c -> Bool
isFinalState (State (_:_) _ _ _ _) = False
isFinalState _ = True

printUCons (Num (UCons f _ t _j) _) = printTerm t

transition :: Herb s c => Prog c -> State c -> Herbrand s (State c)
transition prog (State (c:stack) ustore history id extra) = do
    -- setFlag NoRewindHeap On
--    mapM_ printUCons ustore
--    mapM_ printUCons dstore
    transitionOnCons prog c stack ustore history id extra

transitionOnCons :: Herb s c => Prog c -> StackCons c -> Stack c -> UStore c
		 -> History -> Id -> ExtraState c -> Herbrand s (State c)
-- SOLVE
transitionOnCons prog (BuiltinCons eqs) stack ustore history id extra = do
    newstack <- getWakeUps eqs ustore stack
    result <- callEquations eqs
    if result
      then return (State newstack ustore history id extra)
      else return (FailedBS (extraBStore extra))
-- ACTIVATE
transitionOnCons prog (UserCons ucons) stack ustore history id extra = do
    -- NOTE: Consider only executing the second test if the first fails.
    instore  <- isAlreadyInStore ustore ucons id
    if instore
      then do   -- Set semantics, drop redundant copy
        return (State stack ustore history id extra)
      else do   -- check if it's cyclical
	indstore <- uconsWasDeleted (extraDelStore extra) ucons
	if isJust indstore 
	  then do
	    -- NOTE: we only want to add constraints in the of mono. rec. case
	    stk <- cycleBCons ucons (fromJust indstore)
	    return (State (stk++stack) ustore history id extra)
          else do
	    occs <- getOccs prog ucons
	    return (State ((Active ucons id occs):stack) ((Num ucons id):ustore) history (id+1) extra)
-- REACTIVATE
transitionOnCons prog (Numbered ucons id0) stack ustore history id extra = do
    -- instore  <- isAlreadyInStore ustore ucons id0
    if False -- instore 
      then do   -- Set semantics, delete redundant copy
        return (cleanState stack ustore history id extra [id0])
      else do
	indstore <- uconsWasDeleted (extraDelStore extra) ucons
	if isJust indstore 
	  then do
	    stk <- cycleBCons ucons (fromJust indstore)
	    return (cleanState (stk++stack) ustore history id extra [id0])
	  else do
	    occs <- getOccs prog ucons
	    return (State ((Active ucons id0 occs):stack) ustore history id extra)
	    
transitionOnCons prog active@(Active ucons id0 occs) stack ustore history id extra =
    transitionOnActive prog ucons id0 occs active stack ustore history id extra


-- Pulls out the first argument of each user constraint, and builds an
-- equation unifying them. Use this for breaking cycles arising from 
-- monomorphic recursion.
-- (Append this to the front of the current constraint stack.)
cycleBCons :: Herb s c => UCons c -> DelUCons c -> Herbrand s [StackCons c]
cycleBCons _ (_, False) = return []
cycleBCons (UCons _ a1 uc1 _) (UCons _ a2 uc2 _,_)| a1 < 1 || a2 < 1 = return []
cycleBCons (UCons _ _ uc1 _)  (UCons _ _ uc2 _, _) = do
    t1 <- arg uc1 1
    t2 <- arg uc2 1
    cstr <- doIO $ newCString "="
    eq <- cnst cstr
    tm <- construct eq [t1,t2]
    return [BuiltinCons [BCons tm monoCycleJust]]


transitionOnActive :: Herb s c => Prog c -> UCons c -> Id -> [Occ c] -> StackCons c -> 
                      Stack c -> UStore c -> History -> Id -> ExtraState c -> Herbrand s (State c)
-- DROP
transitionOnActive prog _ _ [] _ stack ustore history id extra = return (State stack ustore history id extra)
-- SIMPLIFY/PROPAGATE/DEFAULT
transitionOnActive prog ucons@(UCons _ _ cons cj) id0 ((occ@(Occ rid sort ocons head body0 isground)):occs) active stack ustore history id extra = do
    cpid0 <- createCP
    status0 <- match cons ocons
    if failed status0
     then do
       rewind cpid0
       return (State ((Active ucons id0 occs):stack) ustore history id extra)              -- DEFAULT
     else do
       (hdmatches,hdmatch,entry) <- matching ustore head (sort==Remain) id0 [rid] history 
       let just = concatJusts (List.map uconsJust (ucons:hdmatch))
	   body = addJust just body0
       rewind cpid0
       if hdmatches 
         then do
            -- rule has fired HERE.
            if isground 
              then do
                nextState sort (body ++ (newStack sort active stack)) ustore history id extra entry
              else do
                cpid1 <- createCP
                newocons <- rename ocons
                newhead  <- renameHeads head
                newstack <- renameBody body (newStack sort active stack)

                setFlag NoRewindHeap On
                rewind cpid1

		----------------------------------------	
		
		-- generate BCons for the BStore
		let stack_bcs = getBuiltinCons newstack
		(match_bcs, mj) <- do cstr <- doIO $ newCString "="
				      eq   <- cnst cstr
				      let hd = newocons : [ h | HCons (UCons _ _ h _) <- newhead ]
					  (ms,js) = unzip ((cons,cj) : [ (m,j) | UCons _ _ m j <- hdmatch ])

					  mk (uc1,uc2) = do
					    (_,arr) <- functor uc1					
					    ts1 <- mapM (arg uc1) [1..arr]
					    ts2 <- mapM (arg uc2) [1..arr]
					    let tss = zipWith (\t1 t2 -> [t1,t2]) ts1 ts2
					    mapM (construct eq) tss
				
				      tmss <- mapM mk (zip hd ms)
				      let tms = concat tmss
				      return (zipWith BCons tms (repeat monoCycleJust), concatJusts js)

		m_bcs <- mapM (uncurry extOrigBCons) [ (t, mj `appendJust` j) | BCons t j <- match_bcs ]
		s_bcs <- mapM (uncurry extOrigBCons) [ (t, mj `appendJust` j) | BCons t j <- stack_bcs ]
		let bcs = m_bcs ++ s_bcs
--		doIO $ putStrLn ("\nm_bcs:\n" ++ prettyLines m_bcs ++ "\n" ++ "\ns_bcs: " ++ pretty s_bcs)
--		let bstore' = bcs ++ bstore
		let extra' = extra { extraBStore = bcs ++ extraBStore extra }
 
		----------------------------------------	

                setFlag NoRewindHeap Off
                setFlag NoOccursCheck On
                unify cons newocons
                bindProgVars newhead hdmatch
                setFlag NoOccursCheck Off
                nextState sort newstack ustore history id extra entry
          else do
            return (State ((Active ucons id0 occs):stack) ustore history id extra)        -- DEFAULT

  where
    -- extracting justifications from matched ucons
    uconsJust (UCons _ _ _ j) = j
    
    -- updating justifications
    addJust :: Just -> Stack c -> Stack c
    addJust j s = List.map addJustStackCons s
      where
	addJustStackCons (UserCons (UCons f n t j0)) = UserCons (UCons f n t (j `appendJust` j0))
	addJustStackCons sc = sc
	

nextState :: Herb s c => OccSort -> Stack c -> UStore c -> History -> Id 
	  -> ExtraState c -> Entry -> Herbrand s (State c)
-- nextState Remain stack ustore history id extra entry = return (State stack ustore (addToFM history entry ()) id extra)
nextState Remain stack ustore history id extra entry = return (State stack ustore (Data.Map.insert entry () history) id extra)
nextState Kill stack ustore history id extra entry   = return (cleanState stack ustore history id extra entry)

newStack :: OccSort -> StackCons c -> Stack c -> Stack c
newStack Kill _ stack        = stack
newStack Remain active stack = (active:stack)

cleanState :: Stack c -> UStore c -> History -> Id -> ExtraState c -> Entry -> State c
cleanState stack ustore history id extra entry = State newstack newustore newhistory id newextra
    where
	newextra = extra { extraDelStore = delucons ++ extraDelStore extra }
        newstack = List.filter (stackConsUsesId entry) stack
	-- note: simplified constraint is removed here!
        (newustore,delucons) = List.partition (storeConsUsesId entry) ustore
--        newhistory = filterFM (entryUsesId entry) history 
        newhistory = filterWithKey (entryUsesId entry) history 

stackConsUsesId :: Entry -> StackCons c -> Bool
stackConsUsesId _ (BuiltinCons _)     = True
stackConsUsesId _ (UserCons _)        = True
stackConsUsesId entry (Numbered _ id) = not (elem id entry)
stackConsUsesId entry (Active _ id _) = not (elem id entry)

storeConsUsesId :: Entry -> UStoreCons c -> Bool
storeConsUsesId entry (Num _ id) = not (elem id entry)

entryUsesId :: Entry -> Entry -> () -> Bool
entryUsesId ids entry _ = entryUsesId' ids entry

entryUsesId' :: Entry -> Entry -> Bool
entryUsesId' [] _ = True
entryUsesId' (id:ids) entry = not ((elem id ids) || (entryUsesId' ids entry))   -- FIX: If compiling to mercury.

bindProgVars :: Herb s c => [HCons c] -> Matching c -> Herbrand s ()
bindProgVars [] _ = return ()
bindProgVars (HActive:head) matching =
    bindProgVars head matching
bindProgVars ((HCons (UCons _ _ hcons _j1)):head) ((UCons _ _ mcons _j2):matching) = do
    status <- unify hcons mcons
    if failed status
      then do
        bug "Binding program vars failed when it should not."
      else do
        bindProgVars head matching

matching :: Herb s c => UStore c -> [HCons c] -> Bool -> Id -> Entry -> History -> Herbrand s (Bool,Matching c,Entry)
matching _ [] ch _ entry history = do
    if ch   -- need to check history?
      then do
--        if elemFM entry history
        if member entry history
          then do
            return (False,[],[])
          else do
            return (True,[],entry)
      else do
        return (True,[],entry)
matching ustore (hcons:head) ch id0 entry history = do
    findMatchingCons ustore ustore hcons head ch id0 entry history

findMatchingCons :: Herb s c => UStore c -> UStore c -> HCons c -> [HCons c] -> Bool -> Id -> Entry -> History -> Herbrand s (Bool,Matching c,Entry)
findMatchingCons _ ustore HActive head ch id0 entry history = matching ustore head ch id0 (id0:entry) history
findMatchingCons [] _ _ _ _ _ _ _ = return (False,[],[])
findMatchingCons ((Num scons@(UCons fntr1 arty1 ucons0 j1) id):ustore) ustore0 hcons@(HCons (UCons fntr2 arty2 hcons0 j2)) head ch id0 entry history = do
    predmatch <- isSameFtrArty fntr1 fntr2 arty1 arty2
    if predmatch && not (elem id entry)         -- FIX if compiling to mercury.
      then do
        cpid <- createCP 
        status <- match ucons0 hcons0
        if failed status
          then do
            rewind cpid
            findMatchingCons ustore ustore0 hcons head ch id0 entry history
          else do
            ans@(foundmatch,match0,entry1) <- matching ustore0 head ch id0 (id:entry) history
            if foundmatch
              then do
                return (foundmatch,(scons:match0),entry1)
              else do
                rewind cpid
                findMatchingCons ustore ustore0 hcons head ch id0 entry history
       else do
         findMatchingCons ustore ustore0 hcons head ch id0 entry history

renameHeads :: Herb s c => [HCons c] -> Herbrand s [HCons c]
renameHeads [] = return []
renameHeads (HActive:head) = renameHeads head
renameHeads ((HCons (UCons fntr arty cons j)):head) = do
    rencons <- rename cons
    renhead <- renameHeads head
    return ((HCons (UCons fntr arty rencons j)):renhead)

renameBody :: Herb s c => Stack c -> Stack c -> Herbrand s (Stack c)
renameBody [] stack = return stack
renameBody (cons:body) stack = do
    newcons <- renameStackCons cons 
    newbody <- renameBody body stack
    return (newcons:newbody)

renameStackCons :: Herb s c => StackCons c -> Herbrand s (StackCons c)
renameStackCons (BuiltinCons eqs) = do
    neweqs <- renameEquations eqs 
    return (BuiltinCons neweqs)
renameStackCons (UserCons (UCons ftr arty cons j)) = do
    newcons <- rename cons
    return (UserCons (UCons ftr arty newcons j))
    
renameEquations :: Herb s c => [BCons c] -> Herbrand s [BCons c]
renameEquations [] = return []
renameEquations ((BCons eq j):eqs) = do
    neweq <- rename eq
    neweqs <- renameEquations eqs 
    return ((BCons neweq j):neweqs)

getOccs :: Herb s c => Prog c -> UCons c -> Herbrand s [Occ c]
getOccs [] _ = return []
getOccs ((Occs ftr1 arty1 occs):prog) ucons@(UCons ftr2 arty2 _ _j) = do
    same <- isSameFtrArty ftr1 ftr2 arty1 arty2
    if same
      then
        return occs
      else
        getOccs prog ucons
            
isSameFtrArty :: Herb s c => c -> c -> CInt -> CInt -> Herbrand s Bool
isSameFtrArty ftr1 ftr2 arty1 arty2 = do
    eq <- eqeq ftr1 ftr2
    return ((arty1 == arty2) && (Success == eq))

getWakeUps :: Herb s c => [BCons c] -> UStore c -> Stack c -> Herbrand s (Stack c)
getWakeUps _ [] stack = do
    return stack
getWakeUps eqs ((Num ucons@(UCons _ _ cons _j) id):ustore) stack0 = do
    needwakeup <- needWakeup eqs cons
    if needwakeup 
      then do
         stack1 <- getWakeUps eqs ustore stack0
         return ((Numbered ucons id):stack1)
      else do
         getWakeUps eqs ustore stack0

needWakeup :: Herb s c => [BCons c] -> c -> Herbrand s Bool
needWakeup [] _ = return False
needWakeup ((BCons eq _j):eqs) cons = do
    shares1 <- share eq cons
    if shares1
      then return True
      else needWakeup eqs cons

callEquations :: Herb s c => [BCons c] -> Herbrand s Bool
callEquations eqs = do
    cpid <- createCP 
    result <- doUnifications eqs
    if result
      then return result
      else do
        rewind cpid
        return False

doUnifications :: Herb s c => [BCons c] -> Herbrand s Bool
doUnifications [] = return True
doUnifications ((BCons eq _j):eqs) = do
    arg1 <- arg eq 1
    arg2 <- arg eq 2
    status <- unify arg1 arg2
    if failed status
      then return False
      else doUnifications eqs


isAlreadyInStore :: Herb s c => UStore c -> UCons c -> Id -> Herbrand s Bool
isAlreadyInStore [] _ _ = return False
isAlreadyInStore ((Num (UCons fntr1 arty1 cons1 _j1) id0):ustore) ucons@(UCons fntr2 arty2 cons2 _j2) id1 
    | id0 == id1 = isAlreadyInStore ustore ucons id1
    | otherwise  = do
	samefntr <- isSameFtrArty fntr1 fntr2 arty1 arty2
        if samefntr
          then do
            status <- eqeq cons1 cons2
            if failed status
              then isAlreadyInStore ustore ucons id1
              else return True
          else isAlreadyInStore ustore ucons id1


-- Used for cycle breaking.
-- If the constraint represents a function call, we check if another constraint 
-- with the same functor is in the given store (which should be the current 
-- dstore.) We also compare justifications to ensure that the constraint being 
-- considered for removal descended from the other.
-- Returns the constraint that was found to match from the dstore (or Nothing 
-- if there was no match), and a flag which indicates whether we should add a
-- new equation in place of this constraint (if its True, then we should.)
--
-- FIXME: The procTC case below (which corresponds to a coinductive reasoning
--	  step) is buggy, so I skip it for now. I think the problem is that the
--	  history contains more than just the constraints which have been
--	  simplified away. Anyway, for programs like f 0 = 0, the inferred type
--	  would contain no Num constraint, whereas f x = 0, would. So,
--	  obviously too much was being removed.
uconsWasDeleted :: Herb s c => UStore c -> UCons c 
		-> Herbrand s (Maybe (DelUCons c))
uconsWasDeleted store ucons@(UCons fntr2 arty2 cons2 j2) = do
    -- First check whether the constraint belongs to a function or a class.
    (tm, ar) <- functor fntr2
    isC <- isCnst tm
    if not isC then return Nothing
      else do
	cnm <- cnstName tm
	nm  <- doIO (peekCString cnm)
	-- doIO $ putStr ("\nnm: " ++ nm ++ "\t\t\tisVarId?" ++ show (isVarId nm) ++ "\n")
	if isVarId nm
	  then procFun store
	  else -- return Nothing 
	       procTC  store
  where

    -- We look for an exact copy, in the history, of the given constraint.
    -- If we find one, we remove/replace this constraint.
    -- FIXME: Currently we just remove the duplicate constraint, but we should
    --	      really replace it with a `True' constraint, suitably justified
    --	      for us to build the required evidence later.
    procTC [] = return Nothing
    procTC ((Num sucons@(UCons fntr1 arty1 cons1 j1) id0):ustore) = do
	stat <- eqeq cons2 cons1
	let same = not (failed stat)
	    j_ok = let (i1:js1) = justLocs j1
		       (i2:js2) = justLocs j2
		   in  i1 /= i2 && js2 `hasSuffix` js1
--	doIO $ putStrLn ("j2  : " ++ show j2 ++ " j1 " ++ show j1)
--	doIO $ putStrLn ("same: " ++ show same ++ " j_ok: " ++ show j_ok)
	if same -- && j_ok 
	  then return (Just (sucons, False))
	  else procTC ustore	      
  
    -- We look trough the history for a constraint with the same predicate
    -- symbol that this constraint must have descended from.
    -- If we find one, we break the cycle.
    procFun [] = {- puts "Nothing" >> -} return Nothing
    procFun ((Num sucons@(UCons fntr1 arty1 cons1 j1) id0):ustore) = do
	samefntr <- isSameFtrArty fntr1 fntr2 arty1 arty2
	let sub = let ls1 = justLocs j1
		      ls2 = justLocs j2
		  in  ls2 `hasPrefix` ls1
{-
	puts ("j2: " ++ show j2)
	puts ("j1: " ++ show j1)
	puts ("sub: " ++ show sub)
	puts ("mono: " ++ show monoAdminJust)
-}	
	if not samefntr 
	  then {- puts "not samefntr" >> -} procFun ustore
	  else if adminJust `subJust` j2
	         then {- puts "match, poly" >> -} return (Just (sucons, False))
		 else if monoAdminJust `subJust` j2 || sub
		        then {- puts "match, mono" >> -} return (Just (sucons, True))
			else procFun ustore
    
    puts = doIO . putStrLn 


--------------------------------------------------------------------------------
-- The rest is the CHR compiler.

compileCHRs :: Herb s c => [Rule c] -> Herbrand s (Prog c)
compileCHRs rules = do 
    eqstr <- doIO (newCString "=")
    eq <- cnst eqstr
    compileRules eq (-1) rules1 []
    where
        rules1 = sortBy ruleCompare rules 

-- Same as compileCHRs but does not reorder any rules.
compileCHRsNoReorder :: Herb s c => [Rule c] -> Herbrand s (Prog c)
compileCHRsNoReorder rules = do
    eqstr <- doIO (newCString "=")
    eq <- cnst eqstr
    compileRules eq (-1) (reverse rules) []

compileRules :: Herb s c => c -> Id -> [Rule c] -> Prog c -> Herbrand s (Prog c)
compileRules _ _ [] prog = return prog
compileRules eq rid (rule:rules) prog0 = do
    prog1 <- compileRule eq rid rule prog0
    compileRules eq (rid-1) rules prog1

compileRule :: Herb s c => c -> Id -> Rule c -> Prog c -> Herbrand s (Prog c)
compileRule eq rid (SimpRule head body js) prog0 = compileRule' eq rid Kill head body js prog0
compileRule eq rid (PropRule head body js) prog0 = compileRule' eq rid Remain head body js prog0

compileRule' :: Herb s c => c -> Id -> OccSort -> [c] -> [c] -> [Just] -> Prog c -> Herbrand s (Prog c)
compileRule' eq rid sort head0 body0 just0 prog0 = do
    (body,isground) <- compileBody eq body0 just0 [] []
    head1 <- termsToHCons head0
    compileHeads head1 [] rid sort body isground prog0 

-- note: justifications belong to constraints at the same list position
compileBody :: Herb s c => c -> [c] -> [Just] -> [BCons c] -> Stack c -> Herbrand s (Stack c,Bool)
compileBody _ [] _js [] stack =  do
    groundstack <- allgroundStackCons stack
    return (stack,groundstack)
compileBody _ [] _js bcons@(_:_) stack = do
    groundbcons <- allgroundBCons bcons
    if groundbcons
      then do
        groundstack <- allgroundStackCons stack
        return (finalstack,groundstack)
      else return (finalstack,False)
    where
        finalstack = ((BuiltinCons bcons):stack)
compileBody eq (c:cs) (j:js) bcons stack = do
    (fntr,arty) <- functor c
    iseq <- isSameFtrArty fntr eq arty 2
    if iseq
      then compileBody eq cs js ((BCons c j):bcons) stack
      else compileBody eq cs js bcons ((UserCons (UCons fntr arty c j)):stack)

compileBody _ _ _ _ _ = bug "compileBody: can't compile (too few justifications?)"

allgroundBCons :: Herb s c => [BCons c] -> Herbrand s Bool
allgroundBCons [] = return True
allgroundBCons ((BCons eq _j):eqs) = do
    ground1 <- ground eq
    if ground1
      then allgroundBCons eqs
      else return False

allgroundStackCons :: Herb s c => Stack c -> Herbrand s Bool
allgroundStackCons [] = return True
allgroundStackCons ((UserCons (UCons _ _ cons _j)):stack) = do
    groundcons <- ground cons
    if groundcons
      then allgroundStackCons stack
      else return False

-- note: head constraints are unjustified
compileHeads :: Herb s c => [HCons c] -> [HCons c] -> Id -> OccSort -> Stack c -> Bool -> Prog c -> Herbrand s (Prog c)
compileHeads [] _ _ _ _ _ prog = return prog
compileHeads ((hcons@(HCons (UCons fntr arty c _j))):head0) head1 rid sort body isground prog = do
    prog1 <- insertOccIntoProg prog fntr arty (Occ rid sort c ((reverse (HActive:head1)) ++ head0) body isground)
    compileHeads head0 (hcons:head1) rid sort body isground prog1

-- note: head constraints are unjustified
termsToHCons :: Herb s c => [c] -> Herbrand s [HCons c]
termsToHCons [] = return []
termsToHCons (c:cs) = do
    (fntr,arty) <- functor c
    hcons0 <- termsToHCons cs
    return ((HCons (UCons fntr arty c noJust)):hcons0)

insertOccIntoProg :: Herb s c => Prog c -> c -> CInt -> Occ c -> Herbrand s (Prog c)
insertOccIntoProg [] fntr arty occ = return [Occs fntr arty [occ]]
insertOccIntoProg ((occscoll@(Occs fntr0 arty0 occs0)):prog) fntr1 arty1 occ = do
    matches <- isSameFtrArty fntr0 fntr1 arty0 arty1
    if matches
      then return ((Occs fntr0 arty0 (occ:occs0)):prog)
      else do
        newprog <- insertOccIntoProg prog fntr1 arty1 occ
        return (occscoll:newprog)

-- More expensive rules first (will be reversed later).
ruleCompare :: Rule c -> Rule c -> Ordering
ruleCompare (SimpRule head1 body1 _) (SimpRule head2 body2 _) = 
    compareHeadBody head2 body2 head1 body1
ruleCompare (SimpRule _ _ _) (PropRule _ _ _) = GT
ruleCompare (PropRule _ _ _) (SimpRule _ _ _) = LT
ruleCompare (PropRule head1 body1 _) (PropRule head2 body2 _) =
    compareHeadBody head2 body2 head1 body1

compareHeadBody :: [c] -> [c] -> [c] -> [c] -> Ordering
compareHeadBody head1 body1 head2 body2 =
    if (cmpheads == EQ)
      then compare (length body1) (length body2)
      else cmpheads
   where
       cmpheads = compare (length head1) (length head2)

-- creates a goal from lists of terms and justifications (which must be of
-- equal length!)
createGoal:: (Eq c, Herb s c) => [c] -> [Just] -> Herbrand s (State c)
createGoal goal js = do
    eqstr <- doIO (newCString "=")
    eq <- cnst eqstr
    (goal1,_) <- compileBody eq goal js [] []
    vss <- mapM fvNonICons goal
    let vs = nub (concat vss)
	extra = initExtraState { extraVars = vs }
--    return (State goal1 [] emptyFM 1 extra)
    return (State goal1 [] empty 1 extra)

--------------------------------------------------------------------------
-- Returns True iff ustore1 and ustore2 are variants w.r.t. vars which
-- cannot be renamed.
variants :: Herb s c => [c] -> UStore c -> UStore c -> Herbrand s Bool
variants vars ustore1 ustore2 = do
    if (length ustore1) == (length ustore2)
      then do   
        cpid <- createCP
        skolemiseList vars
        result <- variants' ustore1 ustore2
        rewind cpid
        return result
      else do
        return False
    where
        skolemiseList [] = return ()
        skolemiseList (v:vars) = do
            skolemise v
            skolemiseList vars

variants' :: Herb s c => UStore c -> UStore c -> Herbrand s Bool
variants' [] _ =
    return True
variants' ((Num ucons _):ustore1) ustore2 = do
    findVariantCons ustore2 [] ustore1 ucons

findVariantCons :: Herb s c => UStore c -> UStore c -> UStore c -> UCons c -> Herbrand s Bool
findVariantCons [] _ _ _ = return False
findVariantCons (numcons@(Num scons@(UCons fntr2 arty2 ucons2 _) _):ustore2) seen ustore1 cons1@(UCons fntr1 arty1 ucons1 _) = do
    predmatch <- isSameFtrArty fntr1 fntr2 arty1 arty2
    if predmatch 
      then do
        cpid <- createCP
        status <- variant ucons1 ucons2
        if failed status
          then do
            rewind cpid
            findVariantCons ustore2 (numcons:seen) ustore1 cons1
          else do
            isvariant <- variants' ustore1 (ustore2++seen) 
            if isvariant
              then do
                return isvariant
              else do
                rewind cpid
                findVariantCons ustore2 (numcons:seen) ustore1 cons1
       else do
         findVariantCons ustore2 (numcons:seen) ustore1 cons1

