--------------------------------------------------------------------------------
--
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
-- Implementor: J.Wazny
-- Maintainer : J.Wazny
--------------------------------------------------------------------------------
-- 
-- | Generates automatically derived instances, which are specified by the
-- `deriving' keyword. This should be invoked during desugaring from the
-- external to internal language.
--
-- FIXME: 
--
--  * Currently we lack support for Read.
--
--  * The error reporting is ad hoc, if presented with a non-derivable
--    class, we bail out. This should probably be checked for earlier
--    (during external AST checking) where it can be handled uniformly
--    with the other kinds of errors.
-- 
--------------------------------------------------------------------------------

module AST.Deriving (
    derive
) where

import Core.BuiltIn
import Misc
import Misc.ErrorMsg

import AST.SrcInfo
import AST.Internal as I
import AST.External as E
import AST.Operators

--------------------------------------------------------------------------------

-- | Generates all the derived instances for the given data dec.
derive :: OpTable -> E.Data -> [I.Dec]
derive ot d@(E.Data _ _ cs (Deriv ds)) = map proc ds
  where
    proc id = case lookup (E.idStr id) trans of 
		Just f  -> f info id_arr d
		Nothing -> let msg = errorMsg info 
				      ["Cannot automatically derive `"++
                                      I.idStr id ++ "' instances"]
			   in  bug msg
      where
	trans = [("Eq", dEq), ("Ord", dOrd), ("Enum", dEnum), 
		 ("Bounded", dBounded), ("Read", dRead), ("Show", dShow ot)]
        info = getSrcInfo id
  
    -- identifiers and arrities
    id_arr :: [(E.Id, Int)]
    id_arr = [ ida | c <- cs, let ida = case c of 
                                    E.Con id ts -> (id, length ts)
                                    E.QCon _ _ id ts -> (id, length ts)
				    E.RecCon id fs -> (id, length fs) 
				    E.RecQCon _ _ id fs -> (id, length fs) ]

--------------------------------------------------------------------------------
-- Helper functions.

-- Takes two expressions of type Bool, and returns the logical and.
andExp :: SrcInfo -> I.Exp -> I.Exp -> I.Exp
andExp info = \a b -> let m1 = let p = I.ConPat info true []
			       in  Match [p,p] (I.VarExp true)
		          m2 = let p = I.VarPat (mkId info "_")
			       in  Match [p,p] (I.VarExp false)
		      in  I.CaseExp info [a, b] [m1, m2]
  where
    true  = mkId info "True"
    false = mkId info "False"

--------------------------------------------------------------------------------

-- Generates an appropriate Eq instance for this type. (Defining (==))
dEq :: SrcInfo -> [(E.Id, Int)] -> E.Data -> I.Dec
dEq info id_arr (E.Data t vs cs _) =
    let -- All of the type's arguments must also be in Eq.
	ctxt = let mkPred v = I.Pred info (mkId "Eq") [v]
                   ps = map (mkPred . I.VarType) vs
               in  I.Ctxt ps
        
	-- The Eq pred, on this type.
	pred = let c  = I.ConType t
                   ts = map I.VarType vs
                   typ= foldl (I.AppType info) c ts
               in  I.Pred info (mkId "Eq") [typ]
        
	-- Generate the pattern matches, with the default `False' case.
	ms   = map mkMatch id_arr ++ [default_match]
        exp  = let a  = I.mkId info "a"
                   b  = I.mkId info "b"
                   e1 = I.VarExp a 
                   e2 = I.VarExp b
               in  abs a (abs b (I.CaseExp info [e1,e2] ms))
        dec  = let lb = I.LetBnd info eq exp
               in  I.ValDec info lb
    
    in  I.InstDec info (I.Inst ctxt pred [dec])

      where
      
        mkId  = I.mkId info
	true  = I.ConExp (mkId "True")
	false = I.ConExp (mkId "False")
        abs   = I.AbsExp info
	app   = I.AppExp info
	eq    = mkId "=="

	-- If none of the other cases match, then it's False (not equal).
	default_match :: I.Match
        default_match = 
            let p = I.VarPat (mkId "_")
            in  I.Match [p,p] false
        
	-- For the given constructor, with arrity as specified, generate the
	-- single case for which the (==) function will return True.
	mkMatch :: (I.Id, Int) -> I.Match
        mkMatch (id, a) = 
            let ss1 = mkStrs 0 a
		ss2 = mkStrs a a

		p1 = I.ConPat info id (map I.VarPat ss1)
                p2 = I.ConPat info id (map I.VarPat ss2)

            in  if a == 0 
		  then -- It's sufficient to match just these constructors.
		       I.Match [p1,p2] true
		       
		  else -- We have to test for equality of sub-expressions.
		       let test  = \a b -> (I.VarExp eq `app` a) `app` b
			   tests = zipWith test (map I.VarExp ss1)
						(map I.VarExp ss2)
			   exp | singleton tests = head tests
			       | otherwise = foldl1 (andExp info) tests
		       in  I.Match [p1,p2] exp
          where
	    mkStrs f n = [ mkId ('x':show m) | m <- [f..f+n-1] ]

            mkVars f n = map (I.VarPat . mkId . ('x':) . show) [f..f+n-1]

--------------------------------------------------------------------------------

-- Generates an appropriate Ord instance for this type. (Defining (<=))
dOrd :: SrcInfo -> [(E.Id, Int)] -> E.Data -> I.Dec
dOrd info id_arr (E.Data t vs cs _) = 
    let -- All of the type's arguments must also be in Ord.
	ctxt = let mkPred v = I.Pred info (mkId "Ord") [v]
                   ps = map (mkPred . I.VarType) vs
               in  I.Ctxt ps
        
	-- The Eq pred, on this type.
	pred = let c  = I.ConType t
                   ts = map I.VarType vs
                   typ= foldl (I.AppType info) c ts
               in  I.Pred info (mkId "Ord") [typ]
        
	-- Generate the pattern matches, with the default `False' case.
        exp  = let a  = I.mkId info "a"
                   b  = I.mkId info "b"
                   e1 = I.VarExp a 
                   e2 = I.VarExp b
		   ms = mkMatches (reverse id_arr) [] e2
               in  abs a (abs b (I.CaseExp info [e1] ms))
        dec  = let lb = I.LetBnd info lteq exp
               in  I.ValDec info lb
    
    in  I.InstDec info (I.Inst ctxt pred [dec])

      where

        mkId  = I.mkId info
	true  = I.ConExp (mkId "True")
	false = I.ConExp (mkId "False")
        abs   = I.AbsExp info
	app   = I.AppExp info
	lteq  = mkId "<="

	-- First list contains all the constructors/arrities we haven't matched
	-- e1 against yet. It's in order from highest value to lowest.
	-- Second list contains those we've already matched e1 against, and
	-- will need to match e2 against.
	-- We create an e1 match out of the head of the first list.
	mkMatches :: [(Id, Int)] -> [(Id, Int)] -> I.Exp -> [Match]
	mkMatches [] _ _ = []
	mkMatches (ida@(id,a):lt_idas) gt_idas e2 = 
	    -- First match e1 (form above) against the current constructor.
	    let ss1 = mkStrs 0 a
		p1  = I.ConPat info id (map I.VarPat ss1)

		-- Now the matching against the 2nd argument to (<=), e2.
		exp = let gt_idas' = reverse gt_idas

			  -- The trivially true cases, i.e. e1 <= e2
			  m_true  = let ps = map ((:[]) . mkTrivConPat) gt_idas'
				    in  map (flip I.Match true) ps
				
			  -- The trivially false case, i.e. e1 > e2
			  m_default = let p = I.VarPat (mkId "_")
				      in  I.Match [p] false
	
			  -- The interesting case, cons. match, go deeper.
			  m_maybe = let ss2= mkStrs a a
					p2 = I.ConPat info id (map I.VarPat ss2)
					test = \a b -> (I.VarExp lteq `app` a)
						       `app` b
					tests = zipWith test (map I.VarExp ss1)
							     (map I.VarExp ss2)
					exp | null tests = true
					    | singleton tests = head tests
					    | otherwise = 
						foldl1 (andExp info) tests
				    in  I.Match [p2] exp
					
		      in  I.CaseExp info [e2] (m_true ++ [m_maybe, m_default])
			
		m  = I.Match [p1] exp
		ms = mkMatches lt_idas (ida:gt_idas) e2
	    in  m : ms
	  where
	    mkStrs f n = [ mkId ('x':show m) | m <- [f..f+n-1] ]

	    mkTrivConPat (id2,a2) = let us = I.VarPat (mkId "_")
				    in  I.ConPat info id2 (replicate a2 us)

--------------------------------------------------------------------------------

dEnum :: SrcInfo -> [(E.Id, Int)] -> E.Data -> I.Dec
dEnum info id_arr (E.Data t vs cs _) | not_ok    = bug "can't derive Enum"
				     | otherwise =
    let -- The Enum pred, on this type.
	pred = let c  = I.ConType t
                   ts = map I.VarType vs
                   typ= foldl (I.AppType info) c ts
               in  I.Pred info (mkId "Enum") [typ]

	decs = [toEnumDec, fromEnumDec,
		enumFromDec, enumFromThenDec, enumFromToDec, enumFromThenToDec]
 
    in  I.InstDec info (I.Inst I.emptyCtxt pred decs)

  where
    not_ok  = not nullary || null id_arr
    nullary = and [ arr == 0 | (_,arr) <- id_arr ]

    con_ids :: [I.Id]
    con_ids = map fst id_arr

    -- helpers
    mkId  = I.mkId info
    app   = I.AppExp info
    abs   = I.AbsExp info
    cse   = I.CaseExp info
    bMap  = I.VarExp (mkId bMapStr)	      -- built-in map
    bLT   = I.VarExp (mkId bLTIntStr)	      -- built-in less-than (<) on Ints
    
    -- lambda-bound variables used
    a = mkId "a"
    b = mkId "b"
    c = mkId "c"
    us = mkId "_"

    -- other functions, constants
    true  = mkId "True"
    false = mkId "False"
    bEnumFromTo     = mkId bEnumFromToIntStr
    bEnumFromThenTo = mkId bEnumFromThenToIntStr
    
    -- automatically derived functions
    toEnumId   = mkId "toEnum"
    fromEnumId = mkId "fromEnum"
    enumFromId	     = mkId "enumFrom"
    enumFromThenId   = mkId "enumFromThen"
    enumFromToId     = mkId "enumFromTo"
    enumFromThenToId = mkId "enumFromThenTo"

    ---------------------------------------- 

    toEnumDec, fromEnumDec :: I.Dec
 
    toEnumDec = 
	let ms  = let mkMatch (id,n) = I.Match [p] l
                	where
                	  p = I.LitPat (I.IntLit info n)
                	  l = I.ConExp id
                                                                  
                  in  map mkMatch (zip con_ids [0..])
                                                                  
	    exp = abs a (cse [I.VarExp a] ms)
	
	in  I.ValDec info (I.LetBnd info toEnumId exp)
 
    fromEnumDec = 
	let ms  = let mkMatch (id,n) = I.Match [p] l
			where
			  p = I.ConPat info id []
			  l = I.LitExp (I.IntLit info n)

		  in  map mkMatch (zip con_ids [0..])

	    exp = abs a (cse [I.VarExp a] ms)

	in  I.ValDec info (I.LetBnd info fromEnumId exp)

    ---------------------------------------- 

    enumFromDec, enumFromThenDec, enumFromToDec, enumFromThenToDec :: I.Dec

    enumFromDec = 
	let lst = I.ConExp (last con_ids)
	    exp = abs a (app (app (I.VarExp enumFromToId) (I.VarExp a)) lst)
	in  I.ValDec info (I.LetBnd info enumFromId exp)


    enumFromThenDec = 
	let exp = let goto = app (app (app (I.VarExp enumFromThenToId) 
					   (I.VarExp a)) 
				      (I.VarExp b))
		      up   = goto (I.ConExp (last con_ids))
		      down = goto (I.ConExp (head con_ids))
		      
		      m1 = I.Match [I.ConPat info true  []] down
		      m2 = I.Match [I.ConPat info false []] up
		      
		      e1 = app (I.VarExp fromEnumId) (I.VarExp a)
		      e2 = app (I.VarExp fromEnumId) (I.VarExp b)
		      e3 = app (app bLT e1) e2
		      e4 = cse [e3] [m1,m2]
		  in  abs a (abs b e4)
	in  I.ValDec info (I.LetBnd info enumFromThenId exp)

    enumFromToDec = 
	let exp = let e1 = app (I.VarExp fromEnumId) (I.VarExp a) 
		      e2 = app (I.VarExp fromEnumId) (I.VarExp b)
		      e3 = app (app (I.VarExp bEnumFromTo) e1) e2
		      e4 = app (app bMap (I.VarExp toEnumId)) e3
		  in  abs a (abs b e4)
	in  I.ValDec info (I.LetBnd info enumFromToId exp)

    enumFromThenToDec = 
	let exp = let e1 = app (I.VarExp fromEnumId) (I.VarExp a) 
		      e2 = app (I.VarExp fromEnumId) (I.VarExp b)
		      e3 = app (I.VarExp fromEnumId) (I.VarExp b)
		      e4 = app (app (app (I.VarExp bEnumFromThenTo) e1) e2) e3
		      e5 = app (app bMap (I.VarExp toEnumId)) e4
		  in  abs a (abs b (abs c e5))
	in  I.ValDec info (I.LetBnd info enumFromThenToId exp)


    
--------------------------------------------------------------------------------

-- NOTE: I assume we've already checked that this type is suitable to
--	 automatically derive Bounded for. 
--	 i.e. either all constructors are nullary, OR 
--	      there's only one constructor
dBounded :: SrcInfo -> [(E.Id, Int)] -> E.Data -> I.Dec
dBounded info id_arr (E.Data t vs cs _) | not_ok    = bug "can't derive Bounded"
					| otherwise = 
    let -- All of the type's arguments must also be in Bounded.
	ctxt = let mkPred v = I.Pred info (mkId "Bounded") [v]
                   ps = map (mkPred . I.VarType) vs
               in  I.Ctxt ps
        
	-- The Bounded pred, on this type.
	pred = let c  = I.ConType t
                   ts = map I.VarType vs
                   typ= foldl (I.AppType info) c ts
               in  I.Pred info (mkId "Bounded") [typ]

    in  -- there are two cases to consider
	if nullary 
          then -- constructors are nullary
	    let generic m f = let exp = I.ConExp (fst (f id_arr))
				  lb  = I.LetBnd info m exp
			      in  I.ValDec info lb
	    
		min  = generic minId head
		max  = generic maxId last
		
	    in  I.InstDec info (I.Inst ctxt pred [min,max])
	
	  else -- single constructor case
	    let (id,arr) = head id_arr
	    
		generic m = let exp = foldl app (I.ConExp id) 
				      (replicate arr (I.VarExp m))
				lb  = I.LetBnd info m exp
			    in  I.ValDec info lb
	    
		min = generic minId
		max = generic maxId

	    in  I.InstDec info (I.Inst ctxt pred [min,max])

  where
    not_ok  = not (nullary || singleton id_arr)
      
    nullary = and [ arr == 0 | (_,arr) <- id_arr ]

    mkId  = I.mkId info
    app   = I.AppExp info
    minId = mkId "minBound"
    maxId = mkId "maxBound"
	
--------------------------------------------------------------------------------

dRead :: SrcInfo -> [(E.Id, Int)] -> E.Data -> I.Dec
dRead info id_arr (E.Data t vs cs _) = bug "Can't derive Read instances yet"


--------------------------------------------------------------------------------

-- Generates an appropriate Ord instance for this type. (Defining showsPrec)
dShow :: OpTable -> SrcInfo -> [(E.Id, Int)] -> E.Data -> I.Dec
dShow ot info _ (E.Data t vs cs _) = 
    let -- All of the type's arguments must also be in Show.
	ctxt = let mkPred v = I.Pred info (mkId "Show") [v]
                   ps = map (mkPred . I.VarType) vs
               in  I.Ctxt ps
        
	-- The Show pred, on this type.
	pred = let c  = I.ConType t
                   ts = map I.VarType vs
                   typ= foldl (I.AppType info) c ts
               in  I.Pred info (mkId "Show") [typ]

	exp  = let ms = map mkMatch cs
	       in  abs d (abs c (cse [I.VarExp c] ms))

	dec = let lb = I.LetBnd info sprec exp
	      in  I.ValDec info lb

    in  -- there are two cases to consider
	I.InstDec info (I.Inst ctxt pred [dec])
	
  where
    -- helpers
    mkId  = I.mkId info
    app   = I.AppExp info
    abs   = I.AbsExp info
    cse   = I.CaseExp info
    cons  = I.VarExp (mkId consStr)
    cat   = I.VarExp (mkId bAppendStr)
    bMap  = I.VarExp (mkId bMapStr)	       -- built-in map
    bGT   = I.VarExp (mkId bGTIntStr)	       -- built-in grtr-than (>) on Ints
    bSucc = I.VarExp (mkId bSuccIntStr)        -- built-in successor on Ints
    
    -- lambda-bound variables used
    d = mkId "d"
    c = mkId "c"
    r = mkId "r"
    s = mkId "t"
    us = mkId "_"

    -- other functions, constants
    true  = mkId "True"
    false = mkId "False"
    sprec = mkId "showsPrec"

    -- Makes the appropriate showsPrec case for the given constructor.
    -- We separate the cases for regular and record-style constructors.
    mkMatch :: E.Con -> I.Match

    -- The regular, non-record case.
    mkMatch (E.QCon _ _ id ts) = mkMatch (E.Con id ts)
    mkMatch (E.Con id ts) = 
	let arr = length ts
	    ss  = mkStrs 0 arr
	    p   = I.ConPat info id (map I.VarPat ss)

	    -- test d against con's prec.
	    e1 = app (app bGT (I.VarExp d)) conPrec

	    -- the un-parenthesised string result
	    e2 = let x1 = I.LitExp (I.StrLit info (show (E.idStr id) ++ " "))
		     x2 = app cat x1
		     x3 = app (I.VarExp sprec) (app bSucc conPrec)
		     x4 = foldr app (I.VarExp r) 
				    (map (app x3) (map I.VarExp ss))
		 in  abs r (app x2 x4)
	    
	    -- the parenthesised string result
	    e3 = let x1 = app cons (char '(')
		     x2 = app cons (char ')')
		     x3 = app e2 (app x2 (I.VarExp r))
		     x4 = app x1 x3
		 in  abs r x4
	    
	    -- result of test
	    ms = [I.Match [I.ConPat info true []] e3,
		  I.Match [I.ConPat info false []] e2]

	    -- the whole RHS
	    e4 = cse [e1] ms

	in  I.Match [p] e4

      where
	char = I.LitExp . I.CharLit info 
      
	mkStrs f n = [ mkId ('x':show m) | m <- [f..f+n-1] ]
    
	conPrec :: I.Exp 
	conPrec = let p = paPrec (lookupPA ot (E.idStr id))
		  in  I.LitExp (I.IntLit info (fromIntegral p))

    -- The record case (almost the same, except for the un-paren. case)
    -- NOTE: the following code depends on the field list being non-empty
    mkMatch (E.RecQCon _ _ id fs) = mkMatch (E.RecCon id fs)
    mkMatch (E.RecCon id fs) | null fs   = mkMatch (E.Con id [])
			     | otherwise = 
	let arr = length fs
	    ss  = mkStrs 0 arr
	    p   = I.ConPat info id (map I.VarPat ss)

	    -- test d against con's prec.
	    e1 = app (app bGT (I.VarExp d)) conPrec

	    -- the un-parenthesised string result
	    e2 = let x1 = I.LitExp (I.StrLit info (show (E.idStr id) ++ " {"))
		     x2 = app cat x1
    
			  -- showsPrec 0 
		     x3 = app (I.VarExp sprec) (I.LitExp (I.IntLit info 0))

		          -- showing a sub-expression
		     fx4 f_id = abs s (abs r 
				(app (app cat (string f_id))      
				     (app (app cat (string "="))
					  (app (app x3 (I.VarExp s)) 
					       (I.VarExp r)))))

			  -- showing a sub-expression, followed by a comma
		     fx5 f_id = abs s (abs r 
				(app (app cat (string f_id))      
				     (app (app cat (string "="))
					  (app (app x3 (I.VarExp s)) 
					       (app (app cons (char ',')) 
						    (I.VarExp r))))))

			  -- now applied to all sub-expressions
		     x6 = let fs' = [ idStr id | E.FieldDef id _ <- fs ]
			      fs1 = map fx4 (init fs')
			      fs2 = fx5 (last fs')
			      es  = map I.VarExp ss
			      r'  = app (app cat (string "} ")) (I.VarExp r)
			  in  foldr app r' (zipWith app (fs1++[fs2]) es)
		     
		 in  abs r (app x2 x6)
	    
	    -- the parenthesised string result
	    e3 = let x1 = app cons (char '(')
		     x2 = app cons (char ')')
		     x3 = app e2 (app x2 (I.VarExp r))
		     x4 = app x1 x3
		 in  abs r x4
	    
	    -- result of test
	    ms = [I.Match [I.ConPat info true []] e3,
		  I.Match [I.ConPat info false []] e2]

	    -- the whole RHS
	    e4 = cse [e1] ms

	in  I.Match [p] e4

      where
	char   = I.LitExp . I.CharLit info 
	string = I.LitExp . I.StrLit info
      
	mkStrs f n = [ mkId ('x':show m) | m <- [f..f+n-1] ]
    
	conPrec :: I.Exp 
	conPrec = let p = paPrec (lookupPA ot (E.idStr id))
		  in  I.LitExp (I.IntLit info (fromIntegral p))

