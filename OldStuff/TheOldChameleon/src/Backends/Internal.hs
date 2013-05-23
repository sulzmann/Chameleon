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
-- | This module defines the AST data structure for Chameleon's internal
-- language. See doc\/internal_AST.txt for details.
--
-- NOTE: 
-- 
-- * Think about moving some of the common parts of the AST out of here and
--   Internal, and put them in a separate module that both import.
--
--------------------------------------------------------------------------------

module Backends.Internal (
    module Backends.Internal, module AST.Common,
    DataType (..), Type (..), Lit (..), Pat (..), PrimVal (..),
    TSchm (..)
)
where

import Misc
import AST.SrcInfo
import qualified AST.Internal as AI
import AST.Internal (DataType (..), Type (..), Lit (..), Pat (..), PrimVal (..), TSchm (..))
import AST.Common


--------------------------------------------------------------------------------

-- A `Prog' really corresponds to the contents of a single file, even though
-- the entire program may be spread across multiple files.
-- NOTE: Currently we only ever process the first module. Haskell only allows
--	 one module per file anyway.
data Prog = Prog [Module]
    deriving (Eq, Show)

pProg :: AI.Prog -> Prog
pProg (AI.Prog ms) = Prog (map pModule ms)

-- a module with a name, export list and local declarations
-- syntax: "module" <module name :: Id> <export_list :: Exports> 
--		    <operator precedence and associativity :: [OpPA]>
--		    <import declarations :: [Import]>
--		    <other declarations :: [Dec]>
data Module = 
    Module	{ moduleId :: Id
		, moduleExports :: Exports
		, moduleImports :: [Import]
		, moduleDecs :: [Dec]
		}
    deriving (Eq, Show)

pModule :: AI.Module -> Module
pModule (AI.Module id exports imports decs t) =
	Module id exports imports (map pDec decs)

----------------------------------------

-- all non-import declarations
-- syntax: see below for specific cases
data Dec = 
    ValDec { decSrcInfo :: SrcInfo, decLetBnd :: LetBnd }
  | DataDec { decSrcInfo :: SrcInfo, decDataType :: DataType, decConss :: [Cons] }
  | PrimDec { decSrcInfo :: SrcInfo, decPrimVal :: PrimVal }
    deriving (Eq, Show)

pDec :: AI.Dec -> Dec
pDec (AI.ValDec si lb) = ValDec si (pLetBnd lb)
pDec (AI.DataDec si dt css) = DataDec si dt (map pCons css)
pDec (AI.PrimDec si p) = PrimDec si p
pDec dec = bug ("pDec: Unexpected declaration " ++ show dec)

-- a nested block of declarations (usually under a `where')
type Where = [Dec]

-- data constructor
-- syntax: "forall" <existential vars :: [Id]> "." <context :: Cnst> "=>" 
--		    <constructor :: DataType>
data Cons = Cons { consSrcInfo :: SrcInfo, consDataType :: DataType }
    deriving (Eq, Show)

pCons :: AI.Cons -> Cons
pCons (AI.Cons si ids cnst dataType) = Cons si dataType

-- expressions
-- syntax: <variable :: Id>
--	 | <constructor :: Id>
--	 | <literal :: Lit>
--	 | <function :: Exp> <argument :: Exp>
--	 | "\" <pattern variable :: Id> "->" <result :: Exp>
--	 | "let" <let binding group :: [LetBnd]> "in" <result :: Exp>
--	 | "case" <scrutinees :: [Exp]> <alternatives :: [Match]>
data Exp = VarExp  Id
	 | ConExp  Id		    -- do we need these?!
	 | LitExp  Lit
	 | AppExp  SrcInfo Exp Exp
	 | AbsExp  SrcInfo Id Exp
	 | LetExp  SrcInfo [LetBnd] Exp
	 | CaseExp SrcInfo [Exp] [Match]
    deriving (Eq, Show)

pExp :: AI.Exp -> Exp
pExp (AI.VarExp id) = VarExp id
pExp (AI.ConExp id) = ConExp id
pExp (AI.LitExp lit) = LitExp lit
pExp (AI.AppExp si e1 e2) = AppExp si (pExp e1) (pExp e2)
pExp (AI.AbsExp si id e) = AbsExp si id (pExp e)
pExp (AI.LetExp si lbs e) = LetExp si (map pLetBnd lbs) (pExp e)
pExp (AI.CaseExp si es ms) = CaseExp si (map pExp es) (map pMatch ms)

-- case alternative/match
-- syntax: <patterns :: [Pat]> "->" <result :: Exp>
data Match = Match [Pat] Exp
    deriving (Eq, Show)

pMatch :: AI.Match -> Match
pMatch (AI.Match ps e) = Match ps (pExp e)

-- let bindings
-- syntax: "let" <variable name :: Id> "=" <body :: Exp>
data LetBnd = LetBnd SrcInfo Id Exp
    deriving (Eq, Show)

pLetBnd :: AI.LetBnd -> LetBnd
pLetBnd (AI.LetBnd si id e) = LetBnd si id (pExp e)
pLetBnd lb = bug ("pLetBnd: Unexpected let binding " ++ show lb)

--------------------------------------------------------------------------------

isValDec d = case d of ValDec _ _ -> True ; _ -> False

----------------------------------------

instance HasSrcInfo Dec where
    getSrcInfo (ValDec   s _ )  = s
    getSrcInfo (DataDec  s _ _) = s

    newSrcInfo s (ValDec _ lb)    = ValDec s lb
    newSrcInfo s (DataDec _ d cs) = DataDec s d cs

instance HasSrcInfo LetBnd where
    getSrcInfo (LetBnd s _ _)	    = s

    newSrcInfo s (LetBnd _ id exp)	    = LetBnd s id exp

instance HasSrcInfo Exp where
    getSrcInfo (VarExp id)     = getSrcInfo id
    getSrcInfo (ConExp id)     = getSrcInfo id
    getSrcInfo (LitExp lit)    = getSrcInfo lit
    getSrcInfo (AppExp s _ _)  = s
    getSrcInfo (AbsExp s _ _)  = s
    getSrcInfo (LetExp s _ _)  = s
    getSrcInfo (CaseExp s _ _) = s

    newSrcInfo s (VarExp id)      = VarExp (newSrcInfo s id)
    newSrcInfo s (ConExp id)	  = ConExp (newSrcInfo s id)
    newSrcInfo s (LitExp lit)	  = LitExp (newSrcInfo s lit)
    newSrcInfo s (AppExp _ e1 e2) = AppExp s e1 e2
    newSrcInfo s (AbsExp _ id e)  = AbsExp s id e
    newSrcInfo s (LetExp _ lb e)  = LetExp s lb e
    newSrcInfo s (CaseExp _ e m)  = CaseExp s e m

