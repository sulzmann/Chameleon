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
-- Simple string error message formatting. For consistency, use these routines 
-- when generating error and warning messages. (At least until the real pretty
-- printer is up and running.)
--
-- NOTE: We should *always* give source locations when reporting errors. 
--	 The non-source versions should be used sparingly.
-- 
--------------------------------------------------------------------------------

module Misc.ErrorMsg (
    errorMsg, errorMsgLine, errorMsgNoSrc,
    warningMsg, warningMsgNoSrc,
    alternatives
)
where

import List

import Misc
import Maybe
import AST.SrcInfo

--------------------------------------------------------------------------------

-- indents all but the first string by n, and flattens the result
-- (putting newlines between all the strings)
indent :: Int -> [String] -> String
indent n [s]    = s
indent n (s:ss) = let gap = replicate n ' '
		  in  newlines (s : map (gap++) ss)

indentAll :: Int -> [String] -> String
indentAll n ss = let gap = replicate n ' '
		 in  newlines (map (gap++) ss)

message :: String -> [String] -> String
message hdr ms = hdr ++ indent (length hdr) (filter (not . null) ms)

--------------------------------------------------------------------------------
-- NOTE: These functions all ignore empty strings in the input list!

errorMsgNoSrc :: [String] -> String
errorMsgNoSrc = message "ERROR: "

errorMsg :: HasSrcInfo a => a -> [String] -> String
errorMsg s strs | anon      = message "" strs'
		| otherwise = message (formatSrcPos info) strs'
  where
    anon  = info == anonSrcInfo || info == builtInSrcInfo
    info  = getSrcInfo s
    strs' = case strs of
		(s:ss) -> ("ERROR: " ++ s) : ss
		[]     -> ["ERROR"]

errorMsgLine :: HasSrcInfo a => a -> [String] -> String
errorMsgLine s | anon	   = message "ERROR: "
	       | otherwise = message (formatSrcPosLine info ++ "ERROR: ") 
  where
    anon  = info == anonSrcInfo || info == builtInSrcInfo
    info  = getSrcInfo s

----------------------------------------

warningMsgNoSrc :: [String] -> String
warningMsgNoSrc = message "Warning: " 

warningMsg :: HasSrcInfo a => a -> [String] -> String
warningMsg s = message (formatSrcPos (getSrcInfo s) ++ "Warning: ")

--------------------------------------------------------------------------------

-- Looks in the list for strings similar to the argument.
-- Returns a string describing these alternatives.
-- This only applies to strings of 3 characters or more (otherwise we get a lot 
-- of useless hits.)
alternatives :: String -> [String] -> String
alternatives s as 
  | length s < 3 = "" 
  | otherwise    = 
    let sims1 = [ ma | ma@(m,a)<- zip (map (similarStrings s) as) as, isJust m ]
	sims2 = sort sims1
	best  = fromJust (fst (head sims2))
	sims3 = take 3 (takeWhile (\(Just m,_) -> m == best) sims2)
	msg | null sims2 = "" 
	    | singleton sims3 = "Did you mean `" ++ snd (head sims3) ++ "'?"
	    | otherwise = let str = commasOr (map (quote . snd) (sort sims3))
			  in  "Did you mean one of " ++ str ++ "?"
    in  msg
	
