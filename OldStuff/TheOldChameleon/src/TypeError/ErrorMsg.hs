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
-- Implementor: J.Wazny
--  Maintainer: J.Wazny
--      Status: - always defaulting to an ANSI target for printing source code
--		- otherwise okay
--------------------------------------------------------------------------------
--
-- Contains routines for generating error messages for reporting type errors.
--
--------------------------------------------------------------------------------

module TypeError.ErrorMsg (
    -- reportAllTypeErrors
    generateTypeErrorMsg,
    generateKindErrorMsg,
    generateSelectiveHL
) where

import List

import Misc
import Misc.Print
import Misc.Error
import Misc.Result
import Misc.ErrorMsg
import qualified Misc.Output.ANSI   as ANSI
import qualified Misc.Output.Plain  as Plain

import AST.SrcInfo
import Core.Name
import Core.InfResult
import Core.Constraint
import Core.ConsOps
import Core.Justify
import Core.Types

--------------------------------------------------------------------------------

reportAllTypeErrors :: SrcTextData -> [InfResult] -> IO ()
reportAllTypeErrors sd rs = do
    let rs' = filter isInfFailure rs
	reps = intersperse (putStrLn "") (map (reportTypeError sd) rs')
    sequence_ reps

----------------------------------------

-- Reports the type error as a text message.
reportTypeError :: SrcTextData -> InfResult -> IO ()
reportTypeError sd (InfSuccess _ _ _) = bug "reportTypeError: not a type error"
reportTypeError sd (InfFailure id c) = do
    let hdr = errorMsg id ["Type error"]
	bcs = cBCons c
    min <- minUnsatSubset bcs
    let ls  = let j  = concatJusts min
		  js = map getJust min
	      in  nub (justLocs j)
 
	s   = printHLLocs sd ls
	src = ANSI.printSpec s 
    putStrLn (hdr ++ "\n" ++ src)
    

--------------------------------------------------------------------------------

-- Generates a standard error message from the source text and an inference
-- result.
generateTypeErrorMsg :: SrcTextData -> InfResult -> IO Error
generateTypeErrorMsg _  (InfSuccess {}) = return notAnError

-- universal variable instantiated
generateTypeErrorMsg sd (InfFailureUniv id v vs (C { cBCons = bcs})) = do
    min <- minInstantiatingSubset v vs bcs
    let nm  = varName v
	ls0 = let j  = concatJusts min
		  js = map getJust min
	      in  nub (justLocs j)	      
    let ls = filter (>0) ls0
    if nameHasRef nm
      then 
	let ref = nameRef nm
	    info  = refInfo ref
	    v_str = refStr  ref
	
	    rc  = (srcRow info, srcCol info)
	    s = printHLLocsPos sd ls [rc]
	    src  = ANSI.printSpec s 
	       -- Plain.printSpec s
	    -- Put in spaces, since errorMsg will remove empty strings.
	    src' = map (\s -> if null s then " " else s) (lines src)
	    hdr  = split80 ("Polymorphic type variable `" ++ v_str ++ 
			    "' (from line " ++ show (srcRow info) ++ 
			    ", col. " ++ show (srcCol info) ++ ") " ++
			    "instantiated by")
	    msg  = errorMsg id (hdr ++ src')
	in  return (mkError id msg)
      else
	let s = printHLLocsPos sd ls []
	    hdr = ["Polymorphic type variable instantiated by"]
	    src = ANSI.printSpec s 
	    src' = map (\s -> if null s then " " else s) (lines src)
	    msg = errorMsg id (hdr ++ src')
	in  return (mkError id msg)


-- universal variable escaped from its scope
generateTypeErrorMsg sd (InfFailureUnivEsc id tt t vs (C {cBCons=bcs})) = do
    let bcs' = (t =+= (TVar tt)) skolConsJust : bcs
    v <- findInstantiated bcs' vs
    min0 <- minInstantiatingSubset v [] bcs'
    let min = dropSkol min0
        nm  = varName v
	ls0 = let j  = concatJusts min
		  js = map getJust min
	      in  nub (justLocs j)	      
    let ls = filter (>0) ls0
    
    if nameHasRef nm
      then 
	let ref = nameRef nm
	    info  = refInfo ref
	    v_str = refStr  ref
	    rc  = (srcRow info, srcCol info)
	    s = printHLLocsPos sd ls [rc]
	    src  = ANSI.printSpec s 
	       -- Plain.printSpec s
	    -- Put in spaces, since errorMsg will remove empty strings.
	    src' = map (\s -> if null s then " " else s) (lines src)
	    hdr  = split80 ("Polymorphic type variable `" ++ v_str ++ 
			    "' (from line " ++ show (srcRow info) ++ 
			    ", col. " ++ show (srcCol info) ++ ") " ++
			    "escapes through locations:")
	    msg  = errorMsg id (hdr ++ src')
	in  return (mkError id msg)
      else        
	let s = printHLLocsPos sd ls []
	    hdr = ["Polymorphic type variable escapes through locations:"]
	    src = ANSI.printSpec s 
	    src' = map (\s -> if null s then " " else s) (lines src)
	    msg = errorMsg id (hdr ++ src')
	in  return (mkError id msg)



generateTypeErrorMsg sd (InfFailureUConsUnmatched id uc) = do
    let hdr = ["Unmatched user constraint " ++ pretty (prettyRename uc) ++ 
	       " from:"]
	ls  = filter (>0) (justLocs (getJust uc))
	s   = printHLLocs sd ls
	src = ANSI.printSpec s
	src'= map (\s -> if null s then " " else s) (lines src)
	msg = errorMsg id (hdr ++ src')
    return (mkError id msg)

-- type conflict
generateTypeErrorMsg sd (InfFailure id (C { cBCons = bcs})) = do
--  putStrLn ("unsat. bcs: " ++ pretty bcs)
    min <- minUnsatSubset bcs
    -- putStrLn ("min: " ++ pretty min)
    -- putStrLn (" vs: " ++ pretty (sort (fv min)))
    let hdr = errorMsg id ["Type error"]
	ls  = let j  = concatJusts min
		  js = map getJust min
	      in  nub (justLocs j)
	s   = printHLLocs sd ls
	src = ANSI.printSpec s 
	      -- Plain.printSpec s
	msg = errorMsg id (["Type error; conflicting sites:"] ++ 
			   lines src)
	err = mkError id msg

    findConflict min
	
    return err
  where
    findConflict :: [BCons] -> IO ()
    findConflict min = do
	let as = pickVar min
	-- putStrLn ("as:\n" ++ unlines (map pretty as))
	test as
      where
	test [] = bug "TypeError.ErrorMsg.test"
	test (a@(v,(b1,b2),bs):as) = do
	    t <- testChoice a
	    case t of
	      Nothing -> test as
	      Just (t1,t2) -> do
		putStrLn (" a: " ++ pretty a)
		putStrLn ("t1: " ++ pretty t1)
		putStrLn ("t2: " ++ pretty t2)
		let eq1 = TVar v =:= t1
		    eq2 = TVar v =:= t2
		min1 <- minImplicantSubset [] (b1:bs) [eq1]
		min2 <- minImplicantSubset [] (b2:bs) [eq2]
		let ls1 = nub (justLocs (concatJusts min1))
		    ls2 = nub (justLocs (concatJusts min2))
		putStrLn ("min1: " ++ pretty min1)
		putStrLn ("min2: " ++ pretty min2)
		putStrLn (" ls1: " ++ pretty ls1)
		putStrLn (" ls2: " ++ pretty ls2)

		let s1   = printHLLocs sd ls1
		    src1 = ANSI.printSpec s1 
		    s2   = printHLLocs sd ls2
		    src2 = ANSI.printSpec s2
		putStrLn ("src1:\n" ++ src1)
		putStrLn ("src2:\n" ++ src2)
		return ()
		
  
    testChoice :: (Var, (BCons,BCons), [BCons]) -> IO (Maybe (Type,Type))
    testChoice (v, (b1,b2), min') = do
	Just [t1] <- project (b1:min') [v]
	Just [t2] <- project (b2:min') [v]
	putStrLn ("(t1,t2): " ++ pretty (t1,t2))
	ok <- unsat [t1 =:= t2]
	if ok 
	  then return (Just (t1,t2))
	  else trace "SKIP" $ return Nothing
  
    -- Given a minimal unsatisfiable set of bcons, picks a variable which 
    -- appears in at least two constraints, and returns:
    -- 1. the variable
    -- 2. two different constraints containing the variable
    -- 3. all the other constraints
    pickVar :: [BCons] -> [(Var, (BCons,BCons), [BCons])]
    pickVar bcs = 
	let alts = map (\v -> [ b | (b,vs) <- bvs, v `elem` vs ]) vs
	in  pick alts
      where
	vs = fv bcs
	bvs = zip bcs (map fv bcs)
	pick [] = []
	pick ([]:as) = pick as
	pick ([bc]:as) = pick as
	pick ((b1:b2:_):as) = t : pick as
	  where
	    t  = (v,(b1,b2),bs)
	    v  = let is =  (intersection (fv b1) (fv b2))
		 in  {- trace ("is: " ++ pretty is) $ -} head is
	    bs = bcs `without` [b1,b2]
    
generateTypeErrorMsg _  res = 
    trace ("generateTypeErrorMsg, unmatched case:\n" ++ show res) $
	return notAnError

--------------------------------------------------------------------------------

-- Kind Error Reporting
generateKindErrorMsg :: String -> SrcTextData -> InfResult -> IO Error
generateKindErrorMsg _ _ (InfSuccess _ _ _) = return notAnError

generateKindErrorMsg isDefault sd (InfFailure id (C { cBCons = bcs})) = do
    min <- minUnsatSubset bcs 
    let hdr = errorMsg id ["Kind error"]
        ls  = let j  = concatJusts min
                  js = map getJust min
              in  nub (justLocs j)      
        s   = printHLLocs sd ls
        src = ANSI.printSpec s              
              -- Plain.printSpec s                  
        msg = let msgHead = case isDefault of
                              (s:str) -> "Kind Error Due to Defaulting of Polymorphic Kind\n" ++ isDefault
                              []      -> "Kind Error" 
              in errorMsg id ([msgHead++"Conflicting sites:"] ++ lines src)
        err = mkError id msg
    return err

-- Interface for selective location highlight printing of a program
-- srcT, selected by input list of program locations ls.
generateSelectiveHL :: SrcTextData -> [Loc] -> String
generateSelectiveHL srcT ls = let pSrc = printHLLocs srcT ls
                              in ANSI.printSpec pSrc
