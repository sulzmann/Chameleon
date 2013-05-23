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
-- This module defines the AST data structure for Chameleon's internal
-- language. See doc/internal_AST.txt for details.
--
-- NOTE: Think about moving some of the common parts of the AST out of here and
--	 Internal, and put them in a separate module that both import.
--
--------------------------------------------------------------------------------

module AST.Internal (
    module AST.Internal, module AST.Common, module AST.SrcInfo
)
where

import List
import Text.PrettyPrint	    -- pretty printer combinators

import Misc
import AST.SrcInfo
import AST.Common

import Misc.Pretty

--------------------------------------------------------------------------------

-- A `Prog' really corresponds to the contents of a single file, even though
-- the entire program may be spread across multiple files.
-- NOTE: Currently we only ever process the first module. Haskell only allows
--	 one module per file anyway.
data Prog = Prog [Module]
    deriving (Eq, Show)

-- a module with a name, export list and local declarations
-- syntax: "module" <module name :: Id> <export_list :: Exports> 
--		    <import declarations :: [Import]>
--		    <other declarations :: [Dec]>
data Module = Module Id Exports [Import] [Dec] ModType
    deriving (Eq, Show)

data ModType = Cmod | Xmod deriving (Eq, Show)
----------------------------------------

-- all non-import declarations
-- syntax: see below for specific cases
-- NOTE: when generating a CHR for an instance with no context, the placeholder
--	 `True' constraint is justified by the SrcInfo of the InstDec.
data Dec = ValDec  SrcInfo LetBnd
	 | DataDec SrcInfo DataType [Cons]
	 | RuleDec SrcInfo Rule
	 | ClassDec SrcInfo Class
	 | InstDec SrcInfo Inst
	 | PrimDec SrcInfo PrimVal
         | ConsDec SrcInfo Constr
    deriving (Eq, Show)

data Constr = ConstrCls Id Type | ConstrData Id Type
    deriving (Eq, Show)

-- a nested block of declarations (usually under a `where')
type Where = [Dec]

-- a primitive identifier (with explicit external-name string)
-- syntax: "primitive" <primitive id :: Id> 
--		       <external name :: String> <type :: TSchm>
data PrimVal = Prim Id String TSchm
    deriving (Eq, Show)


-- class declaration
-- syntax: "class" <context/super classes :: Ctxt> <class predicate :: Pred> "|"
--		   <functional dependencies :: [FunDep]> "where"
--		   <class methods :: [Method]
data Class = Class Ctxt Pred [FunDep] [Method]
    deriving (Eq, Show)

-- class method
-- syntax: <method name :: Id> "::" <type scheme :: TSchm>
data Method = Method Id TSchm
    deriving (Eq, Show)

-- functional dependency
-- syntax: <domain variables :: [Id]> "->" <range variables :: [Id]>
data FunDep = FunDep SrcInfo [Id] [Id]
    deriving (Eq, Show)

-- instance
-- syntax: "instance" <context :: Ctxt> <instance predicate :: Pred> "where"
--		      <instance method declarations :: Where>
data Inst = Inst Ctxt Pred Where
    deriving (Eq, Show)

-- data type
-- syntax: <constructor name :: Id> <type arguments :: [Type]>
data DataType = DataType Id [Type]
    deriving (Eq, Show)

-- data constructor
-- syntax: "forall" <existential vars :: [Id]> "." <context :: Cnst> "=>" 
--		    <constructor :: DataType>
data Cons = Cons SrcInfo [Id] Cnst DataType
    deriving (Eq, Show)

-- CHR rules
-- syntax: <head :: Ctxt> "<=>" <body :: Cnst>
--	 | <head :: Ctxt> "==>" <body :: Cnst>  
data Rule = SimpRule Ctxt Cnst
	  | PropRule Ctxt Cnst
    deriving (Eq, Show)

-- context; a list of predicates
-- syntax: <predicate :: Pred>
--	 | "(" <predicate :: Pred> "," ... "," ... <predicate :: Pred> ")"
data Ctxt = Ctxt [Pred]
    deriving (Eq, Show)

-- constraint; a list of primitives
data Cnst = Cnst [Prim]
    deriving (Eq, Show)

-- predicate
-- syntax: <predicate symbol :: Id> <type arguments :: [Type]>
data Pred = Pred SrcInfo Id [Type]
    deriving (Eq, Show)

-- primitive; either a predicate or an equation
-- syntax: <predicate :: Pred>
--	 | <left type :: Type> "=" <right type :: Type>
data Prim = PredPrim Pred
	  | EqPrim SrcInfo Type Type
    deriving (Eq, Show)

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

-- case alternative/match
-- syntax: <patterns :: [Pat]> "->" <result :: Exp>
data Match = Match [Pat] Exp
    deriving (Eq, Show)

-- patterns
-- syntax: <variable :: Pat>
--	 | <literal :: Pat>
--	 | <constructor name :: Id> <constructor args :: [Pat]>
data Pat = VarPat Id
	 | LitPat Lit
	 | ConPat SrcInfo Id [Pat]
-- reg-exp pattern
	 | AnnPat SrcInfo Id Type
    deriving (Eq, Show)

-- literals 
--    note: All integer literals from the source program become IntegerLits.
--	    IntLits are generate internally only
--	    FloatLits contain a rational representation of the Float.
-- syntax: <integer :: Integer>
--	 | <int :: Int>
--	 | <floating point :: Double>
--	 | <character string :: String>
--	 | <character :: Char>
data Lit = IntegerLit SrcInfo Integer String
	 | IntLit SrcInfo Int
	 | FloatLit SrcInfo Double (Integer, Integer) String
	 | StrLit SrcInfo String
	 | CharLit  SrcInfo Char
    deriving (Eq, Show)

-- let bindings
-- syntax: "let" <variable name :: Id> "=" <body :: Exp>
--	 | "let" <variable name :: Id> <annotation type :: AnnType> 
--		 <typescheme :: TSchm> "=" <body :: Exp>
data LetBnd = LetBnd SrcInfo Id Exp
	    | LetBndAnn SrcInfo Id AnnType TSchm Exp
    deriving (Eq, Show)

-- annotation type
-- syntax: "::"
--	 | ":::"
data AnnType = Univ
	     | Exist
    deriving (Eq, Show)

-- type scheme
-- syntax: <type context :: Ctxt> "=>" <type :: Type>
data TSchm = TSchm Ctxt Type
    deriving (Eq, Show)

-- types
-- syntax: <type variable :: Id>
--	 | <type constructor :: Id>
--	 | <type :: Type> <type :: Type>
data Type  = VarType Id
	   | ConType Id
	   | AppType SrcInfo Type Type
    deriving (Eq, Show)

--------------------------------------------------------------------------------

-- Miscellaneous helper functions, instances etc.

emptyCtxt = Ctxt []
emptyCnst = Cnst []

letBndUAnn = \s id ts e -> LetBndAnn s id Univ ts e
letBndEAnn = \s id ts e -> LetBndAnn s id Exist ts e

letBndId :: LetBnd -> Id
letBndId (LetBnd _ id _) = id
letBndId (LetBndAnn _ id _ _ _) = id

-- True if the given let-binding is annotated
isAnnLetBnd :: LetBnd -> Bool
isAnnLetBnd (LetBnd {})	   = False
isAnnLetBnd (LetBndAnn {}) = True

isValDec d = case d of ValDec {} -> True ; _ -> False

moduleDecs (Module _ _ _ ds _) = ds

addToAllModules :: [Dec] -> Prog -> Prog
addToAllModules ds1 (Prog ms) = Prog (map add ms)
  where
    add :: Module -> Module
    add (Module id exps ims ds2 t) = Module id exps ims (ds1++ds2) t

----------------------------------------

instance HasSrcInfo Dec where
    getSrcInfo (ValDec   s _ )  = s
    getSrcInfo (DataDec  s _ _) = s
    getSrcInfo (RuleDec  s _ )  = s
    getSrcInfo (InstDec  s _ )  = s
    getSrcInfo (ClassDec s _ )  = s
    getSrcInfo (ConsDec  s _ )  = s

    newSrcInfo s (ValDec _ lb)    = ValDec s lb
    newSrcInfo s (DataDec _ d cs) = DataDec s d cs
    newSrcInfo s (RuleDec _ r)    = RuleDec s r 
    newSrcInfo s (InstDec _ i)	  = InstDec s i
    newSrcInfo s (ClassDec _ c)	  = ClassDec s c
    newSrcInfo s (ConsDec _ c)    = ConsDec s c

instance HasSrcInfo LetBnd where
    getSrcInfo (LetBnd s _ _)	    = s
    getSrcInfo (LetBndAnn s _ _ _ _) = s

    newSrcInfo s (LetBnd _ id exp)	    = LetBnd s id exp
    newSrcInfo s (LetBndAnn _ id at ts exp) = LetBndAnn s id at ts exp

instance HasSrcInfo Lit where
    getSrcInfo (IntegerLit s _ _) = s
    getSrcInfo (IntLit s _)	  = s
    getSrcInfo (FloatLit s _ _ _) = s
    getSrcInfo (StrLit s _)	  = s
    getSrcInfo (CharLit s _)	  = s

    newSrcInfo s (IntegerLit _ i str) = IntegerLit s i str
    newSrcInfo s (IntLit _ i)	      = IntLit s i
    newSrcInfo s (FloatLit _ f r str) = FloatLit s f r str
    newSrcInfo s (StrLit _ str)       = StrLit s str
    newSrcInfo s (CharLit _ c)        = CharLit s c
    

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

instance HasSrcInfo Pat where
    getSrcInfo (VarPat id)    = getSrcInfo id
    getSrcInfo (LitPat l)     = getSrcInfo l
    getSrcInfo (ConPat s _ _) = s

    newSrcInfo s (VarPat id)      = VarPat (newSrcInfo s id)
    newSrcInfo s (LitPat l)	  = LitPat (newSrcInfo s l)
    newSrcInfo s (ConPat _ id ps) = ConPat s id ps


instance HasSrcInfo Type where
    getSrcInfo (VarType id)    = getSrcInfo id
    getSrcInfo (ConType id)    = getSrcInfo id
    getSrcInfo (AppType s _ _) = s 

    newSrcInfo s (VarType id)	   = VarType (newSrcInfo s id)
    newSrcInfo s (ConType id)	   = ConType (newSrcInfo s id)
    newSrcInfo s (AppType _ t1 t2) = AppType s t1 t2

instance HasSrcInfo Pred where
    getSrcInfo (Pred s _ _)    = s
    newSrcInfo s (Pred _ id t) = Pred s id t

instance HasSrcInfo Prim where
    getSrcInfo (PredPrim p)   = getSrcInfo p
    getSrcInfo (EqPrim s _ _) = s

    newSrcInfo s (PredPrim p)     = PredPrim (newSrcInfo s p)
    newSrcInfo s (EqPrim _ t1 t2) = EqPrim s t1 t2

--------------------------------------------------------------------------------
-- Pretty Print Instances For Internal AST

indent :: Int -> String
indent n = replicate n ' '

prettyProg :: Prog -> String
prettyProg = pretty

instance Pretty Prog where
    pretty (Prog ms) = newlines (map pretty ms)

instance Pretty Module where
    pretty (Module id xs is ds t ) = 
	"module " ++ pretty id ++ " " ++ pretty xs ++ "\n" ++ 
	prettyLines is ++ "\n" ++ newlines (map pretty ds) ++ "\n" ++
        pretty t

instance Pretty ModType where
    pretty Cmod = ""
    pretty Xmod = ""

instance Pretty Dec where
    pretty (DataDec _ d c) = "data " ++ pretty d ++ " = " ++ pretty c
    pretty (ClassDec _ c)  = "class " ++ pretty c
    pretty (InstDec _ i)   = "instance " ++ pretty i
    pretty (RuleDec _ r)   = "rule " ++ pretty r
    pretty (PrimDec _ p)   = pretty p
    pretty (ValDec _ l)    = prettyIndent 0 l
    pretty (ConsDec _ c)   = "constraint " ++ (pretty c)

instance Pretty Constr where
    pretty (ConstrCls id ty)  = (idStr id) ++ " :: " ++ (pretty ty)
    pretty (ConstrData id ty) = (idStr id) ++ " :: " ++ (pretty ty)

instance Pretty LetBnd where
    prettyIndent n (LetBnd _ id exp) = 
			prettyIndent n id ++ " = " ++ prettyIndent (n+1) exp
    prettyIndent n (LetBndAnn _ id ann schm exp) = 
			pretty id ++ " " ++ pretty ann ++ " " ++ 
			pretty schm ++ "\n" ++ indent n ++ pretty id ++
			    " = " ++ prettyIndent (n+1) exp

multIndent :: Int -> (Int -> a -> String) -> [a] -> String
multIndent n f xs = concat $ intersperse ("\n" ++ indent n) (map (f n) xs)

instance Pretty Exp where
    prettyIndent n e = case e of
	VarExp id -> pretty id
	ConExp id -> pretty id
	LitExp l  -> pretty l

	AbsExp _ id e -> "(\\" ++ pretty id ++ "->" ++ 
      			  prettyIndent n e ++ ")"
      			 
	LetExp _ ls e -> "(let\n" ++ indent (n+2) ++
      		   multIndent (n+2) prettyIndent ls ++ "\n" ++
      		   indent (n+2) ++ "in " ++ prettyIndent (n+5) e ++ ")"
      			 
	CaseExp _ es m -> "case " ++ multIndent n prettyIndent es ++ " of\n" ++ 
      		   indent (n+1) ++ multIndent (n+1) prettyIndent m


	AppExp _ e1@(AppExp _ _ _) e2 ->
      		    prettyIndent n e1 ++ " " ++ prettyIndent n e2

	AppExp _ e1 e2 -> "(" ++ prettyIndent n e1 ++ " " ++ 
				 prettyIndent n e2 ++ ")"

instance Pretty Match where
    prettyIndent n (Match ps e) = pretty ps ++ "->\n" ++ indent (n+1) ++ 
				  prettyIndent (n+1) e

instance Pretty Pat where
   pretty (VarPat id)      = pretty id
   pretty (LitPat lit)     = pretty lit
   pretty (ConPat _ id ps) = pretty id ++ " " ++ prettySpaces ps
   pretty (AnnPat _ id ty) = pretty id ++ "::" ++ pretty ty

instance Pretty AnnType where
   pretty Univ  = "::"
   pretty Exist = ":::"

instance Pretty Type where
   pretty (VarType id)      = pretty id
   pretty (ConType id)      = pretty id
   pretty (AppType _ t1 t2) = "(" ++ pretty t1 ++ " " ++ pretty t2 ++ ")"
   prettySep _ = " "

instance Pretty DataType where
   pretty (DataType id xs) = pretty id ++ " " ++ prettySpaces xs

instance Pretty Pred where
   pretty (Pred _ id ts) = pretty id ++ " " ++ pretty ts  

instance Pretty Prim where
   pretty (PredPrim p)   = pretty p
   pretty (EqPrim _ t1 t2) = pretty t1 ++ " = " ++ pretty t2

instance Pretty Ctxt where
   pretty (Ctxt ps) = case ps of
	[]  -> ""
	[p] -> pretty p ++ " => "
	_   -> "(" ++ prettyCommas ps ++ ") => "

instance Pretty Cnst where
   pretty (Cnst ps) = prettyCommas ps

instance Pretty Cons where
   prettySep _ = "| "
   pretty (Cons _ [] c d)  = pretty c ++ pretty d
   pretty (Cons _ ids c d) = "forall " ++ prettyCommas ids ++ ". " ++ 
				pretty c ++ pretty d

instance Pretty TSchm where
    prettySep _ = " "
    pretty (TSchm c t) = pretty c ++ pretty t

instance Pretty Method where
    pretty (Method id ts) = pretty id ++ " :: " ++ pretty ts
    prettySep _ = "\n"

instance Pretty Class where
    prettySep _ = "\n"
    pretty (Class c p f w) = pretty c ++ pretty p ++ fs ++ ws
      where
	fs = case f of
		[] -> ""
		_  -> " | " ++ pretty f
		
	ws = case w of
		[] -> "" 
		_  -> " where" ++ "\n" ++ indent 1 ++ prettyIndent 1 w

instance Pretty Inst where
    prettySep _ = "\n"
    pretty (Inst c p w) = pretty c ++ pretty p ++ ws
      where
	ws = case w of
		[] -> "" 
		_  -> " where" ++ "\n" ++ indent 1 ++ prettyIndent 1 w


instance Pretty PrimVal where
    pretty (Prim id "" ts) = "primitive " ++ pretty id ++ pretty ts
    pretty (Prim id ex ts) = "primitive " ++ pretty id ++ " \"" ++ ex ++ "\" " 
				++ pretty ts


instance Pretty Rule where
    pretty (SimpRule h t) = pretty h ++ " <=> " ++ pretty t
    pretty (PropRule h t) = pretty h ++ " ==> " ++ pretty t

instance Pretty Lit where       
    pretty (IntegerLit _ _ s) = s
    pretty (FloatLit _ _ _ s) = s
    pretty (CharLit _ c) = ['\'',c,'\'']
    pretty (StrLit _ s)  = '\"' : s ++ "\""

instance Pretty FunDep where
    pretty (FunDep _ ds rs) = prettySpaces ds ++ "->" ++ prettySpaces rs


--------------------------------------------------------------------------------
-- manipulating AST

-- insert expression at given (expression) location
-- i.e. applies current expression at location, to new expression
-- e.g. inserting e into e1 (e2 e3) at 2, yields e1 ((e2 e) e3)
insertExp :: (Loc,Exp) -> Prog -> Prog
insertExp le@(l,e) p = insProg le p
  where
    insProg le (Prog ms) = case thread insModule ms of
			    Nothing  -> Prog ms
			    Just ms' -> Prog ms'

    insModule (Module id e is ds t) = case thread insDec ds of
				      Nothing  -> Nothing
				      Just ds' -> Just (Module id e is ds' t)

    insDec d = case d of
	ValDec s lb -> case insLetBnd lb of
			Nothing  -> Nothing
			Just lb' -> Just (ValDec s lb')
	_ -> Nothing

    insExp e2 = 
	if getSrcLoc e2 == l 
	  then Just (AppExp anonSrcInfo e2 e)
	  else case e2 of
		AppExp s e3 e4 -> 
		    case insExp e3 of
			Just e3' -> Just (AppExp s e3' e4)
			Nothing  -> case insExp e4 of
					Just e4' -> Just (AppExp s e3 e4')
					Nothing  -> Nothing

		AbsExp s id e3 -> case insExp e3 of
				    Just e3' -> Just (AbsExp s id e3')
				    Nothing  -> Nothing

		LetExp s lbs e3-> 
		    case insExp e3 of
			Just e3' -> Just (LetExp s lbs e3')
			Nothing  -> case thread insLetBnd lbs of
					Just lbs' -> Just (LetExp s lbs' e3)
					Nothing   -> Nothing

		CaseExp s es m -> 
		    case thread insExp es of
			Just es' -> Just (CaseExp s es' m)
			Nothing  -> case thread insMatch m of
					Just m' -> Just (CaseExp s es m')
					Nothing -> Nothing

		_ -> Nothing

    insLetBnd lb = case lb of
	LetBnd s id e -> case insExp e of
			    Nothing -> Nothing
			    Just e' -> Just (LetBnd s id e')

	LetBndAnn s id at t e -> case insExp e of
			    Nothing -> Nothing
			    Just e' -> Just (LetBndAnn s id at t e')

    insMatch (Match ps e) = case insExp e of
				Nothing -> Nothing
				Just e' -> Just (Match ps e')

    thread :: (a -> Maybe a) -> [a] -> Maybe [a]
    thread f [] = Nothing
    thread f (a:as) = case f a of
			Nothing -> case thread f as of
				    Nothing  -> Nothing
				    Just as' -> Just (a:as')
			Just a' -> Just (a':as)
			
--------------------------------------------------------------------------------
-- test

s = anonSrcInfo
mkid = anonId 
var = VarExp . mkid
var' n str = VarExp (Id (anonSrcInfo {srcLoc = n}) str str)
app = AppExp s
p1 = Prog [Module (mkid "M") ExAll [] [d1] Cmod] 
  where
    d1 = ValDec s (LetBnd s (mkid "f") e1)
    e1 = (var' 1 "e1") `app` ((var' 2 "e2") `app` (var' 3 "e3"))

e = var' 4 "e4"
