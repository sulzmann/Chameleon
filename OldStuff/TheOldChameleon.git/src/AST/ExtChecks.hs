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
-- | This module provides static checks of the AST data structure for 
-- Chameleon's external language. See doc\external_AST.txt for details.
-- NOTE: The idea is to do as few checks as possible at this point, and to
--	 perform most checks against the internal AST (which is much simpler.)
--
-- We perform the following checks:
--
-- * Each case match has the same number of patterns.
--   This cannot be done on the internal program since separate definition
--   clauses also need to be checked against each other. Because of the
--   possibility of guarded right-hand-sides the pattern matches for
--   individual clauses often do not end up in the same case expression!
--   (We /could/ desugar such that this would never happen, but the internal
--    program representation would be inefficient. i.e. not directly
--    proportional, in terms of size, to the original program.)
--   e.g. f [x] | test1 = e1
--              | test2 = e2
--        f y = y
--   BECOMES: f = \$1 -> let $2 = case $1 of
--       			    [x] -> if test1 then e1
--       				   else if test2 then e2
--       					else $3
--       			    _   -> $3
--       		    $3 = case $1 of
--       			    y -> y
--       			    _ -> patternMatchFailed
--
--
-- * We need to check all the deriving conditions.
--
--------------------------------------------------------------------------------

module AST.ExtChecks
where

import Misc
import AST.SrcInfo
import AST.External

--------------------------------------------------------------------------------

-- | Checks that the number of expressions (scrutinees) is the same as the
-- number of patterns in all matches.
-- Returns the SrcInfo of all case expressions where this is not the case.
checkPatMatches :: Prog -> [SrcInfo]
checkPatMatches (Prog ds) = []

