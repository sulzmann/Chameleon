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
-- Fixes operator precedence and associativity in the external AST. 
-- The result is another external AST without any explicitly parenthesised 
-- expressions (i.e. PIfxAppExp)
--
-- FIXME: We don't check for adjacent non-associative operators! (We probably 
--	  end up treating them as left-associative.)
--
--------------------------------------------------------------------------------

module AST.Operators (
    Assoc(..), Prec, OpInfo, PAInfo(..), OpTable, 
    lookupPA, emptyOpTable, fixOperators
) 
where

import Misc 
import AST.External

--------------------------------------------------------------------------------

-- | Operator associativity
data Assoc = LA	    -- ^ left associative
	   | RA	    -- ^ right associative
	   | NA	    -- ^ not associative
    deriving (Eq, Show)

-- | Operator precedence (0-11)
type Prec = Int

-- | Precedence and associativity, together at last.
data PAInfo = PA { paPrec :: Prec,  -- ^ precedence
		   paAssoc :: Assoc -- ^ associativity
	      }
    deriving Show

-- | Associates an operator name (`IdStr') along with its precedence and
--   associativity.
data OpInfo = Op IdStr PAInfo
    deriving Show

-- | A table of operator information. (`OpInfo')
type OpTable = [OpInfo]

-- | An empty `OpTable'
emptyOpTable :: OpTable
emptyOpTable = []

-- Default prec./assoc. (highest precedence, left associative.)
defaultPA :: PAInfo
defaultPA = PA 10 LA

-- | Given a table of known operator information, find the precedence and
-- associativity of the named operator.
-- If operator isn't listed, use `defaultPA'.
lookupPA :: OpTable -> IdStr -> PAInfo
lookupPA [] x = defaultPA
lookupPA ((Op id pa):ops) x | x == id   = pa
			    | otherwise = lookupPA ops x


--------------------------------------------------------------------------------
-- Given a program, fixes operator precedence.
-- NOTE: We assume that all fixity information is present in the program, in
--	 the form of FixDecs. This includes fixity information from imported
--	 modules. i.e. everything has to be there explicitly.

fixOperators :: Prog -> Prog
fixOperators p = appExpProg (removeParens . fixLeft t . fixRight t) p
  where
    Prog ((Module _ _ _ ds _):_) = p

    t :: OpTable
    t = let fs  = [ f | FixDec _ f <- ds ]
	in  [ Op (idStr id) pa | Fix a p ids <- fs, id <- ids,
				 let pa = PA p (trA a) ] ++ std
      where
	trA a = case a of NonAssoc   -> NA
			  LeftAssoc  -> LA
			  RightAssoc -> RA 

    -- built-ins
    std :: OpTable
    std = [ Op ":" (PA 5 RA) ]
    
--------------------------------------------------------------------------------

-- gets rid of explicit parenthesised infix applications
removeParens :: Exp -> Exp
removeParens e = case e of
	PIfxAppExp s e1 e2 e3 -> IfxAppExp s e1 e2 e3
	e -> e

-- Fix each infix expression wrt. its left sub-expression.
-- First fix the children, then fix this expression.
fixLeft :: OpTable -> Exp -> Exp
fixLeft t e@(IfxAppExp s e1 e2 e3) =
    case (fixLeft t e1, fixLeft t e3) of
	(e1', e3') ->
	    let pe  = prec t e
		pe1 = prec t e1		-- should this be e1'?
		id  = ifxId e
	    in if pe > pe1 || pe == pe1 && idRA t (idStr id)
		then let left  = ifxLeft e1'
			 mid   = ifxMid e1'
			 right = IfxAppExp s (ifxRight e1') e2 e3'
		     in  IfxAppExp s left mid right
		else e
fixLeft _ e = e

-- Fix each infix expression wrt. its right sub-expression.
-- First fix the children, then fix this expression.
fixRight :: OpTable -> Exp -> Exp
fixRight t e@(IfxAppExp s e1 e2 e3) =
    case (fixRight t e1, fixRight t e3) of
	(e1', e3') -> 
	    let pe  = prec t e
		pe3 = prec t e3		-- should this be e3'?
		id  = ifxId e
	    in if pe > pe3 || pe == pe3 && idLA t (idStr id)
		then let left  = IfxAppExp s e1' e2 (ifxLeft e3')
			 mid   = ifxMid e3'
			 right = ifxRight e3'
		     in  IfxAppExp s left mid right
		else e
fixRight _ e = e


--------------------------------------------------------------------------------

prec :: OpTable -> Exp -> Prec
prec t (IfxAppExp _ _ (VarExp id) _) = paPrec (lookupPA t (idStr id))
prec _ _ = 11

assoc :: OpTable -> Exp -> Assoc
assoc t (IfxAppExp _ _ (VarExp id) _) = paAssoc (lookupPA t (idStr id))
assoc _ _ = NA

idLA, idRA, idNA :: OpTable -> IdStr -> Bool
idLA t id = paAssoc (lookupPA t id) == LA
idRA t id = paAssoc (lookupPA t id) == RA
idNA t id = paAssoc (lookupPA t id) == NA

ifxId :: Exp -> Id
ifxId (IfxAppExp _ _ (VarExp id) _) = id
ifxId _ = anonId "NOT AN OPERATOR APPLICATION"

ifxLeft, ifxMid, ifxRight :: Exp -> Exp
ifxLeft  (IfxAppExp _ e1 _ _) = e1
ifxMid   (IfxAppExp _ _ e2 _) = e2
ifxRight (IfxAppExp _ _ _ e3) = e3


isIfx :: Exp -> Bool
isIfx (IfxAppExp _ _ _ _) = True
isIfx _ = False

--------------------------------------------------------------------------------

{-
standardOps = 
    [ (".", (9, RA)), ("!!", (9, LA)),
      ("^", (8, RA)), ("^^", (8, RA)), ("**", (8, RA)),
      ("*", (7, LA)), ("/", (7, LA)), ("quot", (7, LA)), ("rem", (7, LA)), 
	("div", (7, LA)), ("mod", (7, LA)),
      ("+", (6, LA)), ("-", (6, LA)),
      (":", (5, RA)), ("++", (5, RA)), ("\\\\", (5, NA)),
      ("==", (4, NA)), ("/=", (4, NA)), ("<", (4, NA)), ("<=", (4, NA)), 
	(">=", (4, NA)), (">", (4, NA)), ("elem", (4, NA)), 
	("notElem", (4, NA)),
      ("&&", (3, RA)),
      ("||", (2, RA)),
      (">>", (1, LA)), (">>=", (1, LA)),
      ("=<<", (1, RA)),
      ("$", (0, RA)), ("$!", (0, RA)), ("seq", (0, RA)) ]
-}      
      
--------------------------------------------------------------------------------

{- TESTs
 
e = plus (gt (n vb vy) vx) vz


plus x y = nullAnn (IfxAppExp x (nullAnn (VarExp "+")) y)
gt   x y = nullAnn (IfxAppExp x (nullAnn (VarExp ">")) y)
n    x y = nullAnn (IfxAppExp x (nullAnn (VarExp "&&")) y)

pplus x y = nullAnn (IfxAppExp x (nullAnn (VarExp "+")) y)
pgt   x y = nullAnn (IfxAppExp x (nullAnn (VarExp ">")) y)
pand  x y = nullAnn (IfxAppExp x (nullAnn (VarExp "&&")) y)

vx = nullAnn (VarExp "x")
vy = nullAnn (VarExp "y")
vz = nullAnn (VarExp "z")
vb = nullAnn (VarExp "b")

iterateUntilFixed f x = fixed (iterate f x)
    where fixed (x:y:xs) | x == y    = x
			 | otherwise = fixed (y:xs)

-}
