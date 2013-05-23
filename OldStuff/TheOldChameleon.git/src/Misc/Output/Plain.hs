
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
-- Renders plain text slices as strings. i.e. All formatting is ignored.
--
--------------------------------------------------------------------------------

module Misc.Output.Plain
where

import Misc
import Misc.Print

--------------------------------------------------------------------------------

printSpec :: TextSpec -> String
printSpec []   = []
printSpec spec = printAll start spec
  where
    
    printAll :: TextPos -> TextSpec -> String
    printAll _ [] = ""
    printAll p@(TextPos r c) ((TextSlice (TextRegion s e) f t):ss) = 
	let gap  = gapFromTo p s
	    cur  = gap ++ t
	    rest = printAll e ss
	in  cur ++ rest
    
    -- Puts in enough whitespace to get from the first pos. to the second.
    gapFromTo :: TextPos -> TextPos -> String
    gapFromTo (TextPos r1 c1) (TextPos r2 c2) =
	let (r,c1') | r2 > r1   = (replicate (r2 - r1) '\n', 1)
	            | otherwise = ("", c1)
	 
	    c | c1 < c2   = replicate (c2 - c1) ' '
	      | otherwise = ""

	in  r ++ c
    
    print :: TextPos -> TextSlice -> (TextPos, String)
    print p (TextSlice (TextRegion _ e) f t) = (e, t)
    
    -- start pos
    start = TextPos min_row 1 -- 1 min_col
    
    -- the left-most column
    min_col = let cmp (TextPos _ c) (TextPos _ d) = compare c d
		  ps = concat [ [s, e] | TextRegion s e <- map region spec ]
		  TextPos _ c = foldr1 (minBy cmp) ps
	      in  c
    
    -- the top row
    min_row = case head spec of
		TextSlice (TextRegion (TextPos r _) _) _ _ -> r 
