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
-- Calculates all location info. for a desugared program. 
-- i.e. categorises locations by their `type'
-- 
--------------------------------------------------------------------------------

module AST.LocInfo (
    progLocInfo, emptyLocInfo,
    Locs, AST.LocInfo.Match, Matches, LocInfo(..)
) where

import Misc
import AST.Internal as AST

--------------------------------------------------------------------------------

type Locs  = [Loc]
type Match = Locs
type Matches = [AST.LocInfo.Match]

data LocInfo  = LI {superJust,     -- superclass justifications (aka extractors)
                                   -- class (Eq a)_1 => Ord a
                    allinstJust,   -- (all) instance justifications
                                   -- instance (Eq a)_2 => Eq a
                                   -- instance True_3 => Eq Int
                    constinstJust, -- instance True_3 => Eq Int
                    demandedJust,  -- all demanded justifications
                                   -- methodcall_4, functioncall_5, 
                                   -- constructorcall_6
                    annotJust,     -- annotation justifications
                                   -- f :: (Eq a)_7 => ... 
                    patternJust,   -- pattern justifications
                                   -- K_8 x
                    chrJust        -- justifications of user CHRs 
                    :: Locs }
  deriving Show

addCHR   s l = l { chrJust = getSrcLoc s : chrJust l }
addAnnot s l = l { annotJust = getSrcLoc s : annotJust l }
addSuper s l = l { superJust = getSrcLoc s : superJust l }
addAllinst s l = l { allinstJust = getSrcLoc s : allinstJust l }

emptyLocInfo = LI [] [] [] [] [] [] []

--------------------------------------------------------------------------------

progLocInfo :: Prog -> LocInfo
progLocInfo p = liProg emptyLocInfo p

----------------------------------------

liProg :: LocInfo -> Prog -> LocInfo
liProg l (Prog ms) = foldl liModule l ms

liModule l (Module _ _ _ ds _) = foldl liDec l ds

liDec l d = case d of
    ValDec _ lb  -> liLetBnd l lb
    RuleDec _ r  -> liRule l r
    ClassDec _ c -> liClass l c
    InstDec s i	 -> liInst s l i
    _ -> l

liLetBnd l lb = case lb of
    LetBnd _ _ e -> liExp l e
    LetBndAnn _ _ _ ts e -> liExp (liTSchm addAnnot l ts) e

liExp l e = case e of
    VarExp _ -> l { demandedJust = getSrcLoc e : demandedJust l }
    ConExp _ -> l { demandedJust = getSrcLoc e : demandedJust l }
    AppExp _ e1 e2  -> liExp (liExp l e1) e2
    AbsExp _ _  e1  -> liExp l e1
    LetExp _ lbs e1 -> liExp (foldl liLetBnd l lbs) e1
    CaseExp _ es ms -> foldl liMatch (foldl liExp l es) ms
    _ -> l

liMatch l (Match ps e) = foldl liPat (liExp l e) ps

liPat l p = case p of
    ConPat _ _ ps -> let l' = (l { patternJust = getSrcLoc p : patternJust l })
		     in  foldl liPat l' ps
    _ -> l

liTSchm f l (TSchm c t) = liCtxt f l c

liCtxt f l (Ctxt ps) = foldl (liPred f) l ps
liCnst f l (Cnst ps) = foldl (liPrim f) l ps
liPred f l (Pred s _ _) = f s l 
liPrim f l p = case p of
    PredPrim p -> liPred f l p
    _ -> l

liRule :: LocInfo -> Rule -> LocInfo
liRule l r = case r of
    SimpRule _ c -> liCnst addCHR l c
    PropRule _ c -> liCnst addCHR l c

liClass :: LocInfo -> Class -> LocInfo
liClass l (Class c _ _ _) = liCtxt addSuper l c

liInst s l (Inst c _ w) 
    | c == emptyCtxt = l { constinstJust = getSrcLoc s : constinstJust l,
			   allinstJust = getSrcLoc s : allinstJust l }
    | otherwise = liCtxt addAllinst l c
