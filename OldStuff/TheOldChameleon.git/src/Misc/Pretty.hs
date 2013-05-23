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
-- The pretty printer.
-- NOTE: This is used only for displaying internal data, like constraints. When
--	 displaying the source program, we use its original formatting 
--	 (see Misc.Print)
--
--------------------------------------------------------------------------------

module Misc.Pretty 
where

import Foreign
import List

--------------------------------------------------------------------------------

-- NOTE: This may very well change. The `pretty' output will eventually be in
--       some document description format. (So that pretty output can be
--	 composed into new pretty output, as in the old Chameleon pretty
--	 printer.)
class Pretty a where
    pretty :: a -> String
    prettysPrec :: Int -> a -> ShowS
    prettySep :: a -> String
    prettyIndent :: Int -> a -> String

    pretty x          = prettysPrec 0 x ""
    prettysPrec _ x s = pretty x ++ s
    prettySep _ = ", "
    prettyIndent _ x = pretty x

instance (Pretty a, Pretty b) => Pretty (a,b) where
    pretty (a,b) = '(' : pretty a ++ ", " ++ pretty b ++ ")"
    
instance (Pretty a, Pretty b, Pretty c) => Pretty (a,b,c) where
    pretty (a,b,c) = '(': pretty a ++", " ++ pretty b ++", " ++ pretty c ++")"

instance Pretty Char where
    pretty c = [c]
    prettySep _ = ""

instance Pretty a => Pretty [a] where
--    pretty = prettyList ", "
    pretty (x:xs) = prettyList (prettySep x) (x:xs)
    pretty [] = ""

instance Pretty (Ptr a) where
    pretty = show

-- makes a single string of comma separated elements
commas :: [String] -> String
commas = concat . intersperse ", "

spaces :: [String] -> String
spaces = concat . intersperse " "

newlines :: [String] -> String
newlines = concat . intersperse "\n"

doubleNewlines :: [String] -> String
doubleNewlines = concat . intersperse "\n\n"

arrows :: [String] -> String
arrows = concat . intersperse "->"

commasAnd :: [String] -> String
commasAnd [s] = s
commasAnd ss  = commas (init ss) ++ " and " ++ last ss

commasOr  :: [String] -> String
commasOr [s] = s
commasOr ss  = commas (init ss) ++ " or " ++ last ss

quote :: String -> String
quote s = '`' : s ++ "'"

quotes :: [String] -> [String]
quotes = map quote

-- prints a pretty list with the given element separator
prettyList :: Pretty a => String -> [a] -> String
prettyList sep xs  = concat $ intersperse sep (map pretty xs)

prettySpaces :: Pretty a => [a] -> String
prettySpaces = spaces . map pretty

prettyLines :: Pretty a => [a] -> String
prettyLines = newlines . map pretty

prettyCommas :: Pretty a => [a] -> String
prettyCommas = commas . map pretty

