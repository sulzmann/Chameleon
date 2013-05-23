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
-- | This module contains AST elements which share a common representation in 
-- both the external and internal languages. In particular, this includes 
-- module imports and exports, and identifiers.
-- We factor these out in order to eliminate any need to unnecessarily 
-- translate these elements from the external to the internal.
-- 
--------------------------------------------------------------------------------

module AST.Common 
where

import Misc
import AST.SrcInfo 

--------------------------------------------------------------------------------

-- | An identifier 
data Id = Id { idSrcInfo :: SrcInfo, -- ^ source location info.	
	       idStr     :: IdStr,   -- ^ the string name (eventually qualified)
	       idOrigStr :: IdStr    -- ^ the original name 
	  }
    deriving (Eq, Ord, Show, Read) -- {-, Show-})

-- | builds an Id with the same string for both the `idStr' and `idOrigStr'
-- fields
mkId :: SrcInfo -> IdStr -> Id
mkId s x = Id s x x

-- | builds an Id without any known source information (i.e. `anonSrcInfo')
anonId :: IdStr -> Id
anonId = mkId anonSrcInfo

{-
instance Show Id where
    show id = "(Id " ++ show (idSrcInfo id) ++ " " ++ 
		        show (infixParens (idStr id)) ++ ")"
-}

instance Pretty Id where
    pretty = idStr

idStrs = map idStr

instance HasSrcInfo Id where
    getSrcInfo (Id s _ _) = s
    newSrcInfo s (Id _ n o) = Id s n o

--------------------------------------------------------------------------------

-- | An import declaration.
data Import = Import Id Qual Imports
    deriving (Eq, Show, Read)

-- | Represents the optional qualifier in an `Import' dec.
data Qual = Qual Id
	  | Unqual
    deriving (Eq, Show, Read)

-- | The import list (for a single module import.)
data Imports = ImAll
	     | ImSome [ImSpec]
	     | ImHiding [ImSpec]
    deriving (Eq, Show, Read)


-- | Elements of an import list.
-- NOTE: An ImCon could refer to a class or a type (these are syntactically
--	 indistinguishable.)
data ImSpec = ImVar Id				-- import a variable
	    | ImCon Id ConSpec			-- import a type/class
    deriving (Eq, Show, Read)

-- | Individual members\constructors imported along with a type or class.
data ConSpec = AllCon				-- all constructors/methods
	     | SomeCon [Id]			-- some constructors/methods
    deriving (Eq, Show, Read)

----------------------------------------

-- | The export list.
data Exports = ExAll                            -- export everything local 
             | ExSome [ExSpec]                  -- a specific export list
    deriving (Eq, Show, Read)

-- | Individual entities that can appear in the export list.
data ExSpec = ExModule Id                       -- export a module
            | ExVar Id                          -- export a variable
            | ExCon Id ConSpec			-- export a type/class
    deriving (Eq, Show, Read)

--------------------------------------------------------------------------------

imSpecIds :: ImSpec -> [Id]
imSpecIds (ImVar id)	    = [id]
imSpecIds (ImCon id AllCon) = trace ("bug: elements of imported thing `" ++
				     show id ++ "' not imported!") [id]
imSpecIds (ImCon id (SomeCon ids)) = id : ids

instance Pretty Exports where
    pretty ExAll = ""
    pretty (ExSome xs) = "(" ++ prettyCommas xs ++ ")"

instance Pretty ExSpec where
    pretty (ExModule id) = "module " ++ pretty id
    pretty (ExVar id)    = pretty id
    pretty (ExCon id cs) = pretty id ++ pretty cs

instance Pretty ConSpec where
    pretty AllCon = "(..)"
    pretty (SomeCon ids) = "(" ++ prettyCommas ids ++ ")"

instance Pretty Import where
    pretty (Import id (Qual qid) is) = "import qualified " ++ pretty id ++ 
				       " as " ++ pretty qid ++ " " ++ pretty is
    pretty (Import id Unqual is) = "import " ++ pretty id ++ " " ++ pretty is

instance Pretty Imports where	
    pretty ImAll = ""
    pretty (ImSome is)   = "(" ++ prettyCommas is ++ ")"
    pretty (ImHiding is) = "hiding (" ++ prettyCommas is ++ ")"

instance Pretty ImSpec where
    pretty (ImVar id)    = pretty id
    pretty (ImCon id cs) = pretty id ++ pretty cs
