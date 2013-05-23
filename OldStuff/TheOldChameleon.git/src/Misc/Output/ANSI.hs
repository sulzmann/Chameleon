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
-- Renders formatted text slices for output on an ANSI/VT100 terminal.
--
--------------------------------------------------------------------------------

module Misc.Output.ANSI (
    printSpec
) where

import Misc
import Misc.Print   hiding (format)

--------------------------------------------------------------------------------
-- Colours

data Colour = Black 
	    | Red 
	    | Green 
	    | Yellow 
	    | Blue 
	    | Magenta 
	    | Cyan 
	    | White 
	    | Default	    

    deriving (Eq, Ord)


defaultBG = bg Default

-- highlighting of a single piece of text should use colours in the order that
-- they are listed here
stdHighlightColours = [Red, Blue, Green] ++ repeat Black

-- mixing colours
mixColours = mix
mix c1 c2 = case order2 (c1,c2) of
    (k1, k2) | k1 == k2 -> k1
    (Black, k2)	    -> k2
    (Red, Green)    -> Yellow
    (Red, Yellow)   -> Yellow
    (Red, Blue)	    -> Magenta
    (Red, Magenta)  -> Magenta
    (Red, _)	    -> White
    (Green, Yellow) -> Yellow
    (Green, Blue)   -> Cyan
    (Green, Cyan)   -> Cyan
    (Green, _)	    -> White
    (Yellow, Blue)  -> White
    (Blue, k2)	    -> k2
    (Magenta, _)    -> White
    (Cyan, _)	    -> White

--------------------------------
-- Terminal control sequences

fg Black   = "\ESC[30m"
fg Red     = "\ESC[31m"
fg Green   = "\ESC[32m"
fg Yellow  = "\ESC[33m"
fg Blue    = "\ESC[34m"
fg Magenta = "\ESC[35m"
fg Cyan    = "\ESC[36m"
fg White   = "\ESC[37m"
fg Default = "\ESC[39m"

bg Black   = "\ESC[40m"
bg Red     = "\ESC[41m"
bg Green   = "\ESC[42m"
bg Yellow  = "\ESC[43m"
bg Blue    = "\ESC[44m"
bg Magenta = "\ESC[45m"
bg Cyan    = "\ESC[46m"
bg White   = "\ESC[47m"
bg Default = "\ESC[49m"

bold = "\ESC[1m"

defaultTerm = "\ESC[0m"

--------------------------------------------------------------------------------


printSpec :: TextSpec -> String
printSpec []   = []
printSpec spec = defaultTerm ++ 
		 printAll start spec ++ 
		 defaultTerm
  where
    
    printAll :: TextPos -> TextSpec -> String
    printAll _ [] = ""
    printAll p@(TextPos r c) ((TextSlice (TextRegion s e) f t):ss) = 
	let gap  = gapFromTo p s
	    cur  = format TextNormal gap ++ format f t
	    rest = printAll e ss
	in  cur ++ rest
    
    -- Puts in enough whitespace to get from the first pos. to the second.
    gapFromTo :: TextPos -> TextPos -> String
    gapFromTo (TextPos r1 c1) (TextPos r2 c2) =
	let (r,c1') | r2 > r1   = (replicate (r2 - r1) '\n', 1)
	            | otherwise = ("", c1)
	 
	    c | c1 < c2   = replicate (c2 - c1) ' '
			    -- take (c2' - c1) (concat $ repeat "GAP")
	      | otherwise = ""

	in  r ++ c
    
    print :: TextPos -> TextSlice -> (TextPos, String)
    print p (TextSlice (TextRegion _ e) f t) = (e, t)
    
    -- start pos
    start = TextPos min_row 1 -- min_col
    
    -- the left-most column
    min_col = let cmp (TextPos _ c) (TextPos _ d) = compare c d
		  ps = concat [ [s, e] | TextRegion s e <- map region spec ]
		  TextPos _ c = foldr1 (minBy cmp) ps
	      in  c
    
    -- the top row
    min_row = case head spec of
		TextSlice (TextRegion (TextPos r _) _) _ _ -> r 


format :: TextFormat -> String -> String
format f str = case f of
    TextNormal -> bold ++ defaultNL bold str
    TextHL l   -> let esc = bold ++ bg (stdHighlightColours !! l)
		  in  esc ++ defaultNL esc str
    TextDeEmph -> defaultTerm ++ str
    TextMix f1 f2 -> format f1 str	    -- FIXME

  where
    -- return to default mode before newlines
    defaultNL esc "" = ""
    defaultNL esc ('\n':cs) = defaultTerm ++ "\n" ++ defaultNL esc cs
    defaultNL esc (c:cs) = c : defaultNL esc cs

