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
-- This module defines the SrcInfo data structure for internal use. This
-- provides a reference to a location in the source text.
--
--------------------------------------------------------------------------------

module AST.SrcInfo (
    SrcInfo(..), Many(..), 
    anonSrcInfo, builtInSrcInfo, evidenceTransSrcInfo,

    formatSrcPos, formatSrcPosSimple, formatSrcPosLine,
    
    HasSrcInfo, getSrcInfo, newSrcInfo, getSrcLoc,

    SrcInfoTable, mkSrcInfoTable, lookupSrcLoc
)
where

--------------------------------------------------------------------------------

import List
-- deprecated 
-- import Data.FiniteMap
import Data.Map
import Misc

--------------------------------------------------------------------------------

-- a list of items, with source information
data Many a = Many SrcInfo [a]
    deriving (Eq, Show)

-- WARNING: It is *critical* that for SrcInfo that: \x -> read (show x) == x
--	    We depend on this law in the implication solver. It *will* crash if 
--	    this is not the case!
data SrcInfo = SrcInfo { srcLoc :: Loc,		-- a unique number
			 srcFile :: String,	-- filename
			 srcRow :: Row,		-- row
			 srcCol :: Col,		-- column
			 srcOffset :: Int }	-- character offset into file

    deriving (Eq, Ord, Show, Read)

{-
instance Show SrcInfo where
    show s = show (srcLoc s)
-}

anonSrcInfo :: SrcInfo
anonSrcInfo = SrcInfo (-1) "*ANON*" (-1) (-1) (-1)

builtInSrcInfo :: SrcInfo
builtInSrcInfo = SrcInfo (-1) "*BUILTIN*" (-1) (-1) (-1)

evidenceTransSrcInfo :: SrcInfo
evidenceTransSrcInfo = SrcInfo (-1) "*EVIDENCE-TRANS*" (-1) (-1) (-1)

class HasSrcInfo a where
    getSrcInfo :: a -> SrcInfo
    newSrcInfo :: SrcInfo -> a -> a

    newSrcInfo = bug "newSrcInfo not defined for some type!"

instance HasSrcInfo SrcInfo where
    getSrcInfo = id
    newSrcInfo = const

instance HasSrcInfo (Many a) where
    getSrcInfo (Many s _) = s
    newSrcInfo s (Many _ xs) = Many s xs

instance (HasSrcInfo a, HasSrcInfo b) => HasSrcInfo (Either a b) where
    getSrcInfo (Left a)  = getSrcInfo a
    getSrcInfo (Right a) = getSrcInfo a
    
    newSrcInfo s (Left a)  = Left  (newSrcInfo s a)
    newSrcInfo s (Right a) = Right (newSrcInfo s a)

getSrcLoc :: HasSrcInfo a => a -> Loc
getSrcLoc x = case getSrcInfo x of
--  NoSrcInfo -> bug "applied getSrcLoc to something without a src loc"
    s -> srcLoc s


-- returns a string which contains the source position
-- (can be used in error messages where we need to refer to some source loc.)
formatSrcPos :: SrcInfo -> String
formatSrcPos (SrcInfo _ f r c _) = 
    let pos  | c == 1    = show r
	     | otherwise = show (r,c) 
    
	file | List.null f	 = "" 
	     | otherwise = f ++ ":"

    in  file ++ pos ++ ":"

formatSrcPosLine :: SrcInfo -> String
formatSrcPosLine (SrcInfo _ f r c _) = 
    let ln = show r
	file = if List.null f then "" else f ++ ":"
    in  file ++ ln ++ ":"

formatSrcPosSimple :: SrcInfo -> String
formatSrcPosSimple (SrcInfo _ f r c _) = show (r,c) 
   
--------------------------------------------------------------------------------

-- This records a collection of SrcInfos both as a list, and as a finitemap
-- indexed on the source location (srcLoc).
-- data SrcInfoTable = SrcInfoTable [SrcInfo] (FiniteMap Loc SrcInfo)
data SrcInfoTable = SrcInfoTable [SrcInfo] (Map Loc SrcInfo)

instance Show SrcInfoTable where
    show (SrcInfoTable is _) = show is

mkSrcInfoTable :: [SrcInfo] -> SrcInfoTable
mkSrcInfoTable is = 
    let is' = nub is
--	fm  = listToFM [ (srcLoc i, i) | i <- is' ]
        fm  = fromList [ (srcLoc i, i) | i <- is' ]
    in  SrcInfoTable is' fm

-- finds the SrcInfo in the table with the given srcLoc (if it exists)
lookupSrcLoc :: SrcInfoTable -> Loc -> Maybe SrcInfo
lookupSrcLoc (SrcInfoTable _ fm) l = -- lookupFM fm l
                                     Data.Map.lookup l fm
