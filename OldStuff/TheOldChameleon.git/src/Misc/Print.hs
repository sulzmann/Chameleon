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
-- This module contains routines for displaying the original source program,
-- in various styles. e.g. with locations highlighted, or some parts omitted.
--
--------------------------------------------------------------------------------
-- We have the following to work with:
--  - source text: the input program, in its original format
--  - token stream: tokens extracted from the source, with position info.
--  - AST internal + external: program structure with location numbers
--
-- We need to map a location number to a range within the source text.
--  1) Look up the internal AST to find the starting place in the text for that
--     location.
--  2) Find the token at that textual location, and the one immediately
--     following. Ignoring white space and comments, this indicates the textual 
--     range of that source location.
--
-- NOTE: The actual rendering of slices should involve only character 
--	 formatting of the text. It should not include any layout formatting.
--	 This module should make all layout-related decisions. Such decisions
--	 include:  
--	    - what to put between non-adjacent, horizontal neighbours 
--	      (empty space, or perhaps the original text, but de-emphasised)
--	    - what to place between non-adjacent, vertical neighbours 
--	      (empty space, or ellipses, or the original text, de-emphasised)
--
--	 Note: The renderer will place whitespace between non-adjacent regions.
--
-- FIXME: Most of this stuff is implemented in the most straightforward,
--	  least-efficient way imaginable. If it proves slow, then perform the
--	  obvious optimisations.
--
-- FIXME: Currently if the branches of an if-then-else need to be highlighted,
--	  we only highlight the `then'.
--
--------------------------------------------------------------------------------

module Misc.Print (
    SrcTextData, mkSrcTextData,
    TextPos(..), TextRegion(..), TextFormat(..), TextSlice(..), TextSpec,

    emptySlice,
    textLocation,
    prepareSpecCHBlock,

    printHLLocs, printHLLocsPos
) where

import Char
import List

import Misc
import AST.Token
import AST.SrcInfo
import AST.External


--------------------------------------------------------------------------------

-- A record of all the source-related information we need to maintain in order
-- to do flexible printing of the source text.
data SrcTextData = SrcTextData String SrcInfoTable TokenStream
    deriving Show

mkSrcTextData = SrcTextData

--------------------------------------------------------------------------------

-- row, column text position
data TextPos = TextPos Int Int
    deriving (Eq, Ord)

instance Show TextPos where
    show (TextPos a b) = show (a,b)
 
startPos = TextPos 1 1
nextRow (TextPos r c)  = TextPos (r+1) c
nextCol (TextPos r c)  = TextPos r (c+1)
firstRow (TextPos r c) = TextPos 1 c
firstCol (TextPos r c) = TextPos r 1

----------------------------------------
 
-- indicates a range of positions from the first to just before the second
-- i.e. it's [p1,p2)
-- NOTE: we maintain the invariant that p1 <= p2
data TextRegion = TextRegion { start :: TextPos, end :: TextPos }
	        | NoTextRegion
    deriving (Eq, Ord)

instance Show TextRegion where
    show (TextRegion s e) = show (s,e)
    show NoTextRegion = "()"

-- a single slice of text to print, and its format
data TextSlice = TextSlice { region :: TextRegion,
			     format :: TextFormat,
			     text   :: String }
    deriving (Eq, Ord, Show)

-- Builds a TextSlice without any text in it
emptySlice :: TextFormat -> TextRegion -> TextSlice
emptySlice f r = TextSlice r f ""

plainSlice :: TextRegion -> TextSlice
plainSlice r = TextSlice r TextNormal ""

-- expresses which formatted slices to print
type TextSpec  = [TextSlice]

-- various text formatting options
-- TextNormal - text has the normal, or default appearance
-- TextHL n - highlighted text; all highlighted text belonging to the same `n'
--	      (highlighting group) will be formatted in the same way, e.g.
--	      highlighted in the same colour
-- TextDeEmph - de-emphasises the text 
-- TextMix f1 f2 - text is formatted in a combination of formats f1 and f2
data TextFormat = TextNormal
		| TextHL Int
		| TextDeEmph 
		| TextMix TextFormat TextFormat
    deriving (Eq, Ord, Show)


--------------------------------------------------------------------------------

-- As below, but omits the additional row, column positions.
printHLLocs :: SrcTextData -> [Loc] -> TextSpec
printHLLocs sd ls = printHLLocsPos sd ls []

-- Given source text data, a list of locations to highlight and a list of row,
-- column positions to also display, returns a spec. containing the source with 
-- those locations highlighted/displayed.
printHLLocsPos :: SrcTextData -> [Loc] -> [(Int,Int)] -> TextSpec
printHLLocsPos sd@(SrcTextData _ sit ts) ls rcs = 
    let rs = nub (map (textLocation sd) ls) 
	s  = map (emptySlice (TextHL 0)) rs ++ 
	     map (emptySlice TextNormal) extra_rs
	s' = prepareSpecCHBlock sd s
    in  {- trace ("\nrs: " ++ show rs ++ 
	       "\ns :\n" ++ showLines s ++
	       "\ns':\n" ++ showLines s') -} s'
  where
    extra_rs = [ TextRegion p1 p2 | (r,c) <- rcs, let p1 = TextPos r c
						      p2 = nextCol p1 ]

--------------------------------------------------------------------------------

-- Does all the processing and preparation of a Spec. 
-- After this it's ready to be rendered.
prepareSpec :: String -> TextSpec -> TextSpec
prepareSpec str = cleanupTextSpec . fillTextSpec0 str . normaliseTextSpec

-- Also filters out Chameleon comments
prepareSpecCH :: String -> TextSpec -> TextSpec
prepareSpecCH str = cleanupTextSpecFilt replaceCHComments . fillTextSpec0 str .
		    normaliseTextSpec


prepareSpecCHBlock :: SrcTextData -> TextSpec -> TextSpec
prepareSpecCHBlock (SrcTextData src _ _) = prepareSpecCHBlock' src

-- As above, but fills in the gaps between non-adjacent regions
prepareSpecCHBlock' :: String -> TextSpec -> TextSpec
prepareSpecCHBlock' str = completeTextSpec0 str .
			  cleanupTextSpecFilt replaceCHComments . 
			  fillTextSpec0 str .
			  normaliseTextSpec

--------------------------------------------------------------------------------

-- Takes the source text, and a text spec., and fills in the text fields of the
-- spec with the appropriate source strings.
fillTextSpec :: String -> TextPos -> TextSpec -> TextSpec
fillTextSpec str p spec = [ TextSlice r f t | TextSlice r f _ <- spec,
					      let t = takeRegion str p r ]

-- As above, but assumes that the string starts at the startPos: (1,1)
fillTextSpec0 :: String -> TextSpec -> TextSpec
fillTextSpec0 str spec = fillTextSpec str startPos spec


-- Removes trailing whitespace from all slices in the spec, and updates the end
-- positions of slice ranges.
cleanupTextSpec :: TextSpec -> TextSpec
cleanupTextSpec spec = 
    [ TextSlice (TextRegion s e) f t' | TextSlice (TextRegion s _) f t <- spec,
      let rev = dropWhile (isSpace . fst) (reverse (textWithPos t s)),
      let (e,t') = case rev of 
			[]	-> (s, "")
			(c,p):_ -> (incCol p, reverse (map fst rev)) ]
  where
    -- FIXME: it's a hack (because this may not be a position in the
    --	      original source) but it should work
    incCol (TextPos r c) = TextPos r (c+1)

-- As above, but also takes a string transforming function, which is applied
-- first, before any whitespace removal. This function will typically replace
-- comments in the string with spaces.
-- NOTE: This function must NOT change the length of the string.
cleanupTextSpecFilt :: (String -> String) -> TextSpec -> TextSpec
cleanupTextSpecFilt f spec = 
    cleanupTextSpec [ TextSlice r m (f t) | TextSlice r m t <- spec ]

-- NOTE: all comment blocks are guaranteed well-formed by this stage
replaceCHComments :: String -> String
replaceCHComments "" = ""
replaceCHComments ('{':'-':cs) = ' ' : ' ' : dropBlock 1 cs
  where
    dropBlock 1 ('-':'}':cs) = ' ' : ' ' : cs 
    dropBlock n ('-':'}':cs) = ' ' : ' ' : dropBlock (n-1) cs
    dropBlock n ('{':'-':cs) = ' ' : ' ' : dropBlock (n+1) cs
    dropBlock n (c:cs) | isSpace c = c : dropBlock n cs
		       | otherwise = ' ' : dropBlock n cs
    dropBlock _ "" = bug "replaceCHComments: comment block not closed"
    
replaceCHComments ('-':'-':cs) = 
    let rep = length (takeWhile (/='\n') cs)
	cs' = drop rep cs
	gap = replicate rep ' ' 
	new = ' ' : ' ' : gap
    in  new ++ replaceCHComments cs'
replaceCHComments (c:cs) = c : replaceCHComments cs


-- Given a TextSpec that contains some number of, possibly spaced-out, distant 
-- regions of text, fills in the gaps between those regions, returning a
-- visually complete version of the source string.
-- NOTE : These additional `filler' regions should be de-emphasised.
completeTextSpec :: String -> TextPos -> TextSpec -> TextSpec
completeTextSpec str p [] = []
completeTextSpec str p spec@(s:ss) = -- fill (beginning spec)
    fill (start)
  where
    start = maybe spec (:spec) (beginning s)

{-  
    -- Add in the preceding text from the start of the first line.
    beginning [] = []
    beginning s1ss@(s1@(TextSlice (TextRegion s@(TextPos r c) _) _ _):ss) 
	| c > 1 = let rgn = TextRegion (TextPos r 1) s
		      t   = takeRegion str p rgn
		      s0  = TextSlice rgn f t
		  in  s0 : s1 : ss
	| otherwise = s1ss
-}

    beginning (TextSlice (TextRegion s@(TextPos r c) _) _ _) 
	| c > 1 = let rgn = TextRegion (TextPos r 1) s
		      t   = takeRegion str p rgn
		      s0  = TextSlice rgn f t
		  in  Just s0 
	| otherwise = Nothing


    fill []  = []

    -- Add in the rest of the text until the end of the last line.
    fill [s1@(TextSlice (TextRegion _ e@(TextPos r c)) _ _)] =  
			let rgn = TextRegion e (TextPos r maxBound) -- hack
			    -- We don't want the last character - '\n'
			    t   = init' (takeRegion str p rgn)
			    s2  = TextSlice rgn f t
			in  s1 : [s2]
			
    fill (s1@(TextSlice (TextRegion _ e@(TextPos r1 c1)) _ _):
	  ss@(s2@(TextSlice (TextRegion s@(TextPos r2 c2) _) _ _):_))
	| bigVGap e s = let -- fill in the text after s1
			    s1s = fill [s1]
			    -- the space between the regions
			    p1 = TextPos (r1+1) 1
			    p2 = TextPos (r2-1) 1
			    r  = TextRegion p1 p2
			    t  = "..."
			    sgap = TextSlice r f t
			    -- fill in the text preceding s2
			in  case beginning s2 of
				Nothing -> s1s ++ sgap : fill ss
				Just s3 -> s1s ++ sgap : s3 : fill ss
			
	| e < s	      = let r  = TextRegion e s
			    t  = takeRegion str p r
			    s2 = TextSlice r f t
			in  s1 : s2 : fill ss 

	| otherwise = s1 : fill ss

    init' [] = []
    init' xs = init xs
			
    f = TextDeEmph

    bigVGap p1 p2 = vgapSize p1 p2 >= 3
    vgapSize (TextPos r1 _) (TextPos r2 _) = r2 - r1
    
completeTextSpec0 :: String -> TextSpec -> TextSpec
completeTextSpec0 str spec = completeTextSpec str startPos spec

----------------------------------------

-- Takes a list of possibly overlapping, unordered TextSlices and returns a new 
-- list of ordered, non-overlapping slices representing the same text region 
-- with the same formatting.
-- (NOTE: later slices have precedence over earlier ones.)
normaliseTextSpec :: TextSpec -> TextSpec
normaliseTextSpec = split . sort
  where
    split (s1@(TextSlice r1 f1 t1) : tts@(s2@(TextSlice r2 f2 t2) : ts))
	| r1 `contains` r2 = 
		let s1' = let r = TextRegion (start r1) (start r2)
			  in  TextSlice r f1 (takeRegion t1 (start r1) r)
		    s2' = s2
		    s3' = let r = TextRegion (end r2) (end r1)
			  in  TextSlice r f1 (takeRegion t1 (end r2) r)
		in  s1' : (insert s2' $ insert s3' ts)
		
	| r1 `overlaps` r2 = 
		let s1' = let r = TextRegion (start r1) (start r2)
			  in  TextSlice r f1 (takeRegion t1 (start r1) r)
		    s2' = s2
		in  s1' : s2' : ts
	
	| otherwise = s1 : split tts

    split [s] = [s]
    split []  = []

-- True if the first region completely contains the second
contains :: TextRegion -> TextRegion -> Bool
contains NoTextRegion _ = False
contains _ NoTextRegion = False
contains (TextRegion p1 p2) (TextRegion q1 q2) = p1 <= q1 && p2 >= q2

-- True if the first region overlaps the second (it may contain it)
overlaps :: TextRegion -> TextRegion -> Bool
overlaps NoTextRegion _ = False
overlaps _ NoTextRegion = False
overlaps (TextRegion p1 p2) (TextRegion q1 q2) = p1 <= q1 && p2 >= q1 ||
					         p1 <= q2 && p2 >= q2


-- Takes a starting position, and a string and returns a list of characters
-- from that string, labelled with their text position.
textWithPos :: String -> TextPos -> [(Char, TextPos)]
textWithPos "" p = []
textWithPos (c:cs) p
    | c == '\n' = (c,p) : textWithPos cs (nextRow (firstCol p))
    | otherwise = (c,p) : textWithPos cs (nextCol p)


-- Given a string, and its starting position, returns the part of the string in
-- the given region.
-- NB: The end position is just after the end of the text region.
takeRegion :: String -> TextPos -> TextRegion -> String
takeRegion str p (TextRegion p1 p2) = 
    let tp  = textWithPos str p
	tp' = takeWhile ((<p2) . snd) (dropWhile ((<p1) . snd) tp)
    in  map fst tp'

--------------------------------------------------------------------------------

textLocation :: SrcTextData -> Loc -> TextRegion
textLocation (SrcTextData _ sit ts) l = textLocation' sit ts l

-- Given a SrcInfo table, the token stream and a location, returns the range of 
-- text positions which represent that location in the source.
textLocation' :: SrcInfoTable -> TokenStream -> Loc -> TextRegion
textLocation' sit ts l = case lookupSrcLoc sit l of
    Nothing -> NoTextRegion
    Just i  -> let ps = filter (/=noSrcPos) (map tokenSrcPos ts)
	       in  find ps
      where
	r = srcRow i
	c = srcCol i
	
	find ((_,r1,c1):tts@((_,r2,c2):ts)) 
	    | r1 == r && c1 == c = let p1 = TextPos r1 c1
				       p2 = TextPos r2 c2
				   in  TextRegion p1 p2
	    | otherwise = find tts
	    
        find _ = NoTextRegion

--------------------------------------------------------------------------------


