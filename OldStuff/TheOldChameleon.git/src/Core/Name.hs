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
-- Internal names, which keep track of their source information.
--
--------------------------------------------------------------------------------

module Core.Name (
    Name(..), NameRef(..), mkName, mkFreeName, mkLocName,
    nameLoc, nameHasRef, idToName
)
where

import Misc
import AST.SrcInfo
import AST.Common

--------------------------------------------------------------------------------

-- an (internal) name, with reference info.

-- WARNING: It is *critical* for Name that: \x -> read (show x) == x
--          We depend on this law in the implication solver. It *will* crash if
--          this is not the case!
data Name = Name { nameRef :: NameRef,		-- ref. to the original name
		   nameStr :: String }		-- current name
    deriving (Show, Read)


-- A reference from a name that's currently being used back to an original name
-- in the program source. Use NoNameRef in the case where the name is
-- introduced during the compilation process, and has no direct reference to
-- an original source name.
data NameRef = NoNameRef 

	     -- should match the srcLoc of some SrcInfo in the AST
	     | LocNameRef { refLoc :: Loc } 
						
	     | NameRef { refInfo :: SrcInfo,	-- source location information
			 refStr  :: String }	-- original source name
    deriving (Eq, Ord, Show, Read)

-- WARNING: We depend on these specific definitions of Eq/Ord when converting
-- variables to and from Herbie terms. Odd things will happen if the
-- NameRef component of the names is tested. (Because sometimes we change it
-- behind the scenes, but expect the changed variable to be treated the same as
-- the original.)
instance Eq Name where
    n1 == n2 = nameStr n1 == nameStr n2

instance Ord Name where
    n1 <= n2 = nameStr n1 <= nameStr n2


nameHasRef :: Name -> Bool
nameHasRef (Name { nameRef = NameRef {} } ) = True
nameHasRef _ = False

-- extracts a source location from a name
nameLoc :: Name -> Loc
nameLoc (Name r _) = nameRefLoc r

-- extracts a source location from a name ref
nameRefLoc :: NameRef -> Loc
nameRefLoc NoNameRef	  = noLoc
nameRefLoc (LocNameRef l) = l
nameRefLoc (NameRef i _)  = srcLoc i

-- a completely new name with no source information
mkFreeName :: String -> Name
mkFreeName = Name NoNameRef

mkLocName :: String -> Loc -> Name
mkLocName str l = Name (LocNameRef l) str

mkName :: String -> SrcInfo -> String -> Name
mkName str0 s str1 = Name (NameRef s str0) str1

idToName :: Id -> Name
idToName id = mkName (idStr id) (idSrcInfo id) (idOrigStr id)

instance Pretty Name where
    pretty (Name _ s) = s
