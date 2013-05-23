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
--
-- | This module removes the parts of the internal AST 
-- (defined in AST.Internal) which are not part of the core backend language 
-- (as in Backends.Internal).
-- 
--------------------------------------------------------------------------------

module Backends.Cleanup (
  cleanupAST
) where

import AST.Internal

--------------------------------------------------------------------------------

-- | Filters out everything but `ValDec's and `DataDec's. 
-- Also removes type annotations.
cleanupAST :: Prog -> Prog
cleanupAST = cProg

----------------------------------------

cProg :: Prog -> Prog
cProg (Prog ms) = Prog (map cModule ms)

cModule :: Module -> Module
cModule (Module id xs is ds t) = Module id xs is (cDecs ds) t

cDecs :: [Dec] -> [Dec]
cDecs = concatMap cDec

cDec :: Dec -> [Dec]
cDec d = case d of
	    ValDec  s lb -> [ValDec s (cLetBnd lb)]
	    DataDec {}	 -> [d]
	    PrimDec {}	 -> [d]
	    _	         -> []

cLetBnd :: LetBnd -> LetBnd
cLetBnd (LetBnd s id e)	       = LetBnd s id (cExp e)
cLetBnd (LetBndAnn s id _ _ e) = LetBnd s id (cExp e)

cExp :: Exp -> Exp
cExp e = case e of 
	    VarExp _	-> e
	    ConExp _	-> e
	    LitExp _	-> e
	    AppExp s e1 e2  -> AppExp s (cExp e1) (cExp e2)
	    AbsExp s id e1  -> AbsExp s id (cExp e1)
	    LetExp s lbs e1 -> LetExp s (map cLetBnd lbs) (cExp e1)
	    CaseExp s es ms -> CaseExp s (map cExp es) (map cMatch ms)

cMatch :: Match -> Match
cMatch (Match ps e) = Match ps (cExp e)
