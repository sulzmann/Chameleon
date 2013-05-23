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
-- This module defines the AST data structure for Chameleon's external
-- language. See doc/external_AST.txt for details.
--
-- NOTE: Think about moving some of the common parts of the AST out of here and
--	 Internal, and put them in a separate module that both import.
--
--------------------------------------------------------------------------------

module AST.External (
    module AST.External, module AST.Common
)
where

import Maybe

import Misc
import AST.SrcInfo
import AST.Common
import Misc.Pretty
--------------------------------------------------------------------------------

data Prog = Prog [Module]
    deriving (Eq, Show)

-- a module with a name, export list and local declarations
data Module = Module Id Exports [Import] [Dec] ModType
--            | Xmodule Id Exports [Import] [Dec] -- todo: will be removed soon
    deriving (Eq, Show)

data ModType = Cmod | Xmod deriving (Eq, Show)

hasXModule :: Prog -> Bool
hasXModule (Prog [(Module _ _ _ _ Cmod)]) = False
hasXModule (Prog [(Module _ _ _ _ Xmod)]) = True


----------------------------------------

data Dec  = RuleDec SrcInfo Rule
	  | DataDec SrcInfo Data		-- data type 
	  | TypeDec SrcInfo TSyn 		-- type synonym
	  | AnnDec  SrcInfo Sig			-- a type signature/annotation 
	  | ExtDec  SrcInfo Extern		-- external declaration
	  | ValDec  SrcInfo [Def]		-- function binding
	  | PatDec  SrcInfo PatBnd		-- pattern binding
	  | OverDec SrcInfo Over		-- overload declaration
	  | ClassDec SrcInfo Class		-- class declaration
	  | InstDec  SrcInfo Inst		-- instance declaration
	  | FixDec  SrcInfo  Fixity		-- fixity declaration
	  | PrimDec SrcInfo PrimVal		-- primitive declaration
          | ConsDec SrcInfo Constr              -- constraint declaration (Internal Representation)
          | ExtConsDec SrcInfo Pred             -- external constraint declaration
    deriving (Eq, Show)

type IFace = Id

data Fixity = Fix OpAssoc OpPrec [Id]
    deriving (Eq, Show)
    
type OpPrec  = Int
data OpAssoc = NonAssoc
	     | LeftAssoc 
	     | RightAssoc
    deriving (Eq, Show)

-- a primitive identifier (with explicit external-name string)
data PrimVal = Prim Id String TSchm
    deriving (Eq, Show)

data Over = Over0   Id
	  | OverDef Sig [Def]
    deriving (Eq, Show)

data Class = Class Ctxt Pred [FunDep] Where
           | AFDClass Ctxt Pred [FunDep] [AFDDec] Where
    deriving (Eq, Show)

data AFDDec = AFDDec SrcInfo Id [Id] Id
    deriving (Eq, Show)

data FunDep = FunDep SrcInfo [Id] [Id] 
    deriving (Eq, Show)

data Inst = Inst Ctxt Pred Where
          | AFDInst Ctxt Pred [AFDDef] Where
    deriving (Eq, Show)

data AFDDef = AFDDef SrcInfo Id [Type] Type
    deriving (Eq, Show)

data Extern = VarExt  Sig			-- external var./constructor
	    | TConExt Id			-- external type constructor
    deriving (Eq, Show)
 
data Def = Def Id [Pat] RHS Where
    deriving (Eq, Show)

data PatBnd = PatBnd Pat RHS Where
    deriving (Eq, Show)

data RHS  = RHS1 Exp				-- single expression
	  | RHSG [GdExp]			-- guarded expression(s)
    deriving (Eq, Show)

type Guard = Exp
data GdExp = GdExp SrcInfo Guard Exp
    deriving (Eq, Show)

type Where = [Dec]
 
data Exp  = VarExp Id
          | ConExp Id
	  | LitExp Lit
	  | NegExp SrcInfo Exp
	  | AbsExp SrcInfo [Pat] Exp
	  | AppExp SrcInfo Exp Exp
	  | IfxAppExp  SrcInfo Exp Exp Exp		    -- e1 `e2` e3
	  | PIfxAppExp SrcInfo Exp Exp Exp		    -- parens
	  | LetExp  SrcInfo [Dec] Exp
	  | CaseExp SrcInfo Exp [CaseAlt]
	  | DoExp   SrcInfo [Stmt]
	  | IfExp   SrcInfo Exp SrcInfo Exp Exp	    -- cond and branches have
						    -- separate locations
	  | AnnExp  SrcInfo Exp AnnType TSchm
	  | TupExp  SrcInfo [Exp]
	  | ListExp SrcInfo (Many Exp)		    -- extra info is for site 
						    -- of elem unifier
	  | ListCompExp SrcInfo Exp [Stmt]
	  | RecExp Id [FieldBind]		    -- record construct
	  | UpdExp Exp [FieldBind]		    -- record update
	  | SecLeftExp  SrcInfo Exp Exp			-- (e op)
	  | SecRightExp SrcInfo Exp Exp			-- (op e)
	  | EnumFromExp       SrcInfo Exp		-- [n..]
	  | EnumFromToExp     SrcInfo Exp Exp		-- [n..l]
	  | EnumFromThenExp   SrcInfo Exp Exp		-- [n,m..]
	  | EnumFromThenToExp SrcInfo Exp Exp Exp	-- [n,m..l]
    deriving (Eq, Show)


data CaseAlt = CaseAlt SrcInfo Pat RHS Where
    deriving (Eq, Show)	     

data Stmt = GenStmt  SrcInfo Pat Exp
	  | QualStmt SrcInfo Exp
	  | LetStmt  SrcInfo [Dec]	
    deriving (Eq, Show)


-- NOTE: we store both value and string representations for floats and ints
data Lit  = IntegerLit   SrcInfo Integer String 
	  | FloatLit SrcInfo Double (Integer, Integer) String  
	  | CharLit  SrcInfo Char	
	  | StrLit   SrcInfo String
    deriving (Eq, Show)


data TSyn = TSyn Id [Id] Type			-- lhs cons and args -> type
    deriving (Eq, Show)

data Sig  = Sig Id AnnType TSchm		-- type sig
    deriving (Eq, Show)

data TSchm = TSchm Ctxt Type
    deriving (Eq, Show)

data AnnType = Univ				-- ::
	     | Exist				-- :::
	     | Reg				-- :*:
    deriving (Eq, Show)


data Data = Data Id [Id] [Con] Deriv 
	  | DataKindAnn Id [Type] [Con] Deriv
    deriving (Eq, Show)

data Deriv = Deriv [Id]				-- deriving
    deriving (Eq, Show)

    
-- qualified data constructor: name, exist. variables, context, args
data Con = Con  Id [Type]
	 | QCon [Id] Cnst Id [Type]
	 | RecCon  Id [FieldDef]		-- record-style
	 | RecQCon [Id] Cnst Id [FieldDef]
    deriving (Eq, Show)

data FieldDef = FieldDef Id Type
    deriving (Eq, Show)

data FieldBind = FieldBind SrcInfo Id Exp
    deriving (Eq, Show)

data Rule = PropRule Ctxt Cnst
	  | SimpRule Ctxt Cnst
    deriving (Eq, Show)

data Ctxt = Ctxt [Pred]
    deriving (Eq, Show)

data Cnst = Cnst [Prim]
    deriving (Eq, Show)

data Pred = Pred SrcInfo Id [Type]
    deriving (Eq, Show)

data Prim = PredPrim Pred
          | EqPrim SrcInfo Type Type
    deriving (Eq, Show)

data Type = VarType Id
          | ConType Id
	  | ArrType SrcInfo Type Type
	  | AppType SrcInfo Type Type
	  | TupType SrcInfo [Type]
	  | ListType SrcInfo Type
	  | UnionType SrcInfo [Type]            --  | type  {- regexp type -}
	  | StarType SrcInfo Type               --  * type  {- regexp type -} 
	  | OptionType SrcInfo Type		--  ? type  {- regexp type -}
          | EmpType SrcInfo                     -- {} type {- regexp type -}
          | PhiType                             -- empty language type {- regexp type -}
          | AnnType SrcInfo Id Type
          | FuncType SrcInfo Id [Type]          -- Type Function - From Associated Type Synonyms.
    deriving (Eq, Show)

data Pat  = VarPat Id
	  | LitPat Lit
	  | AsPat  SrcInfo Id Pat
	  | ConPat SrcInfo Id [Pat]
	  | TupPat SrcInfo [Pat]
	  | ListPat SrcInfo [Pat]
	  | LabPat Id [FieldPat]		-- labeled pattern
	  | AnnPat SrcInfo Id Type		-- type annotated pattern {- regexp pat -}
    deriving (Eq, Show)

data FieldPat = FieldPat SrcInfo Id Pat
    deriving (Eq, Show)

data Constr = ConstrCls Id Type | ConstrData Id Type    -- constraint <Id> :: <Kind> , where Kind==Type 
    deriving (Eq, Show)
--------------------------------------------------------------------------------

instance HasSrcInfo a => HasSrcInfo [a] where
    getSrcInfo []    = anonSrcInfo
    getSrcInfo (x:_) = getSrcInfo x

instance HasSrcInfo Dec where
    getSrcInfo (RuleDec s  _) = s
    getSrcInfo (DataDec s  _) = s
    getSrcInfo (TypeDec s  _) = s
    getSrcInfo (AnnDec  s  _) = s  
    getSrcInfo (ExtDec  s  _) = s  
    getSrcInfo (ValDec  s  _) = s
    getSrcInfo (PatDec  s  _) = s  
    getSrcInfo (OverDec s  _) = s
    getSrcInfo (ClassDec s _) = s  
    getSrcInfo (InstDec  s _) = s
    getSrcInfo (FixDec  s _)  = s
    getSrcInfo (PrimDec  s _) = s
    getSrcInfo (ConsDec s _)  = s
    getSrcInfo (ExtConsDec s _) = s

instance HasSrcInfo Def where
    getSrcInfo (Def id _ _ _) = getSrcInfo id

instance HasSrcInfo PatBnd where
    getSrcInfo (PatBnd pat _ _) = getSrcInfo pat

instance HasSrcInfo Pred where
    getSrcInfo (Pred s _ _) = s

instance HasSrcInfo Prim where
    getSrcInfo (PredPrim p)   = getSrcInfo p
    getSrcInfo (EqPrim s _ _) = s

instance HasSrcInfo Type where
    getSrcInfo (VarType id) = getSrcInfo id
    getSrcInfo (ConType id) = getSrcInfo id
    getSrcInfo (ArrType s _ _) = s
    getSrcInfo (AppType s _ _) = s
    getSrcInfo (TupType s _  ) = s
    getSrcInfo (ListType s _ ) = s

instance HasSrcInfo Pat where
    getSrcInfo (VarPat id)    = getSrcInfo id
    getSrcInfo (LitPat lit)   = getSrcInfo lit
    getSrcInfo (ConPat s _ _) = s
    getSrcInfo (TupPat s _)   = s
    getSrcInfo (ListPat s _)  = s
    getSrcInfo (LabPat id _)  = getSrcInfo id
    getSrcInfo (AnnPat s _ _) = s


instance HasSrcInfo Exp where
    getSrcInfo exp = case exp of
	VarExp id    -> getSrcInfo id
	ConExp id    -> getSrcInfo id
	LitExp l     -> getSrcInfo l
	NegExp s _   -> s
        AbsExp s _ _ -> s
        AppExp s _ _ -> s
        IfxAppExp  s _ _ _ -> s
        PIfxAppExp s _ _ _ -> s	 
        LetExp  s _ _ -> s
        CaseExp s _ _ -> s
        DoExp   s _ -> s
	IfExp   s _ s' _ _ -> s	    -- WARNING: 2nd SrcInfo not returned!
        AnnExp  s _ _ _ -> s
        TupExp  s _ -> s
        ListExp s _ -> s		 
        ListCompExp s _ _ -> s
        SecLeftExp  s _ _ -> s		 
        SecRightExp s _ _ -> s		 
        EnumFromExp       s _	  -> s
        EnumFromToExp     s _ _	  -> s
        EnumFromThenExp   s _ _	  -> s
        EnumFromThenToExp s _ _ _ -> s
	_ -> anonSrcInfo

instance HasSrcInfo CaseAlt where
    getSrcInfo (CaseAlt s _ _ _) = s

instance HasSrcInfo GdExp where
    getSrcInfo (GdExp s _ _) = s

instance HasSrcInfo Lit where
    getSrcInfo (IntegerLit s _ _) = s
    getSrcInfo (FloatLit s _ _ _) = s
    getSrcInfo (CharLit  s _)   = s
    getSrcInfo (StrLit   s _)   = s

instance HasSrcInfo Sig where
    getSrcInfo (Sig id _ _) = getSrcInfo id
--------------------------------------------------------------------------------
-- collect the src infos out of AST e recursively
class CollectSrcInfos e where
    collectSrcInfos :: e -> [SrcInfo]

instance CollectSrcInfos Id where
    collectSrcInfos i = [(idSrcInfo i)]


instance CollectSrcInfos a => CollectSrcInfos (Many a) where
    collectSrcInfos (Many s as) = [s] ++ (collectSrcInfos as)

instance CollectSrcInfos a => CollectSrcInfos [a] where
    collectSrcInfos []    = []
    collectSrcInfos (x:xs) = (collectSrcInfos x)++(collectSrcInfos xs)

instance CollectSrcInfos Prog where
    collectSrcInfos (Prog ms) = collectSrcInfos ms

instance CollectSrcInfos Module where
    collectSrcInfos (Module id ex ims decs _) =  -- ignore the export and imports?
	(idSrcInfo id):(collectSrcInfos decs)
{-
    collectSrcInfos (Xmodule id ex ims decs) = 
        (idSrcInfo id):(collectSrcInfos decs)
-}

instance CollectSrcInfos Dec where
    collectSrcInfos (RuleDec s  _) = [s]
    collectSrcInfos (DataDec s  d) = [s] ++ (collectSrcInfos d)
    collectSrcInfos (TypeDec s  _) = [s]
    collectSrcInfos (AnnDec  s sig) = [s]
    collectSrcInfos (ExtDec  s  _) = [s]
    collectSrcInfos (ValDec  s defs) = [s]++(collectSrcInfos defs)
    collectSrcInfos (PatDec  s  _) = [s]
    collectSrcInfos (OverDec s  _) = [s]
    collectSrcInfos (ClassDec s _) = [s]
    collectSrcInfos (InstDec  s _) = [s]
    collectSrcInfos (FixDec  s _)  = [s]
    collectSrcInfos (PrimDec  s _) = [s]

instance CollectSrcInfos Def where
    collectSrcInfos (Def id pats rhs wh) = 
	(collectSrcInfos id) ++
	(collectSrcInfos pats) ++
	(collectSrcInfos rhs) ++
	(collectSrcInfos wh)

instance CollectSrcInfos PatBnd where
    collectSrcInfos (PatBnd pat rhs wh) = 
	(collectSrcInfos pat) ++ 
	(collectSrcInfos rhs) ++
	(collectSrcInfos wh)


instance CollectSrcInfos Ctxt where
    collectSrcInfos (Ctxt preds) = collectSrcInfos preds

instance CollectSrcInfos Cnst where
    collectSrcInfos (Cnst prims) = collectSrcInfos prims

instance CollectSrcInfos Pred where
    collectSrcInfos (Pred s id tys) = [s] ++ (collectSrcInfos id) ++ (collectSrcInfos tys)

instance CollectSrcInfos Prim where
    collectSrcInfos (PredPrim p)   = collectSrcInfos p
    collectSrcInfos (EqPrim s t1 t2) = [s] ++ (collectSrcInfos [t1,t2])

instance CollectSrcInfos Type where
    collectSrcInfos (VarType id) = collectSrcInfos id
    collectSrcInfos (ConType id) = collectSrcInfos id
    collectSrcInfos (ArrType s t1 t2) = [s] ++ (collectSrcInfos t1) ++ (collectSrcInfos t2)
    collectSrcInfos (AppType s t1 t2) = [s] ++ (collectSrcInfos t1) ++ (collectSrcInfos t2)
    collectSrcInfos (TupType s tys) = [s] ++ (collectSrcInfos tys)
    collectSrcInfos (ListType s t) = [s] ++ (collectSrcInfos t)
    collectSrcInfos (UnionType s tys) = [s] ++ (collectSrcInfos tys)
    collectSrcInfos (StarType s t) = [s] ++ (collectSrcInfos t)
    collectSrcInfos (OptionType s t) = [s] ++ (collectSrcInfos t)
    collectSrcInfos (EmpType s) = [s]
    collectSrcInfos PhiType = []

instance CollectSrcInfos Pat where
    collectSrcInfos (VarPat id)    = collectSrcInfos id
    collectSrcInfos (LitPat lit)   = collectSrcInfos lit
    collectSrcInfos (AsPat s id pat) =
	[s] ++ (collectSrcInfos id) ++ (collectSrcInfos pat)
    collectSrcInfos (ConPat s id pats) = 
	[s] ++ (collectSrcInfos id) ++ (collectSrcInfos pats)
    collectSrcInfos (TupPat s pats)   = [s] ++ (collectSrcInfos pats)
    collectSrcInfos (ListPat s pats)  = [s] ++ (collectSrcInfos pats)
    collectSrcInfos (LabPat id fpats)  = collectSrcInfos id ++ (collectSrcInfos fpats)
    collectSrcInfos (AnnPat s id ty) = 
	[s] ++ (collectSrcInfos id) ++ (collectSrcInfos ty)


instance CollectSrcInfos FieldPat where
    collectSrcInfos (FieldPat s id pat) =
	[s] ++ (collectSrcInfos id) ++ (collectSrcInfos pat)


instance CollectSrcInfos Exp where
    collectSrcInfos exp = case exp of
	VarExp id    -> collectSrcInfos id
	ConExp id    -> collectSrcInfos id
	LitExp l     -> collectSrcInfos l
	NegExp s e   -> [s] ++ (collectSrcInfos e)
        AbsExp s pats e -> [s] ++ (collectSrcInfos pats) ++ (collectSrcInfos e)
        AppExp s e1 e2 -> [s] ++ (collectSrcInfos e1) ++ (collectSrcInfos e2)
        IfxAppExp  s e1 e2 e3 -> [s] ++ (collectSrcInfos [e1,e2,e3])
        PIfxAppExp s e1 e2 e3 -> [s] ++ (collectSrcInfos [e1,e2,e3])
        LetExp  s decs e -> [s] ++ (collectSrcInfos decs) ++ (collectSrcInfos e)
        CaseExp s e cas -> [s] ++ (collectSrcInfos e) ++ (collectSrcInfos cas)
        DoExp   s stmts -> [s] ++ (collectSrcInfos stmts)
	IfExp   s e1 s' e2 e3 -> [s,s'] ++ (collectSrcInfos [e1,e2,e3])
        AnnExp  s e at tschm -> [s] ++ (collectSrcInfos e) ++ (collectSrcInfos at) ++ (collectSrcInfos tschm)
        TupExp  s es -> [s] ++ (collectSrcInfos es)
        ListExp s me -> [s] ++ (collectSrcInfos me)
        ListCompExp s e stmts -> [s] ++ (collectSrcInfos e) ++ (collectSrcInfos stmts)
        SecLeftExp  s e1 e2 -> [s] ++ (collectSrcInfos [e1,e2])
        SecRightExp s e1 e2 -> [s] ++ (collectSrcInfos [e1,e2])
        EnumFromExp       s e	  -> [s] ++ (collectSrcInfos e)
        EnumFromToExp     s e1 e2 -> [s] ++ (collectSrcInfos [e1,e2])
        EnumFromThenExp   s e1 e2 -> [s] ++ (collectSrcInfos [e1,e2])
        EnumFromThenToExp s e1 e2 e3 -> [s] ++ (collectSrcInfos [e1,e2,e3])
	_ -> []

instance CollectSrcInfos CaseAlt where
    collectSrcInfos (CaseAlt s pat rhs wh) = 
	[s] ++ (collectSrcInfos pat) ++ (collectSrcInfos rhs) ++ (collectSrcInfos wh)

instance CollectSrcInfos Stmt where
    collectSrcInfos (GenStmt s pat e) = [s] ++ (collectSrcInfos pat) ++ (collectSrcInfos e)
    collectSrcInfos (QualStmt s e) = [s] ++ (collectSrcInfos e)
    collectSrcInfos (LetStmt s decs) = [s] ++ (collectSrcInfos decs)

instance CollectSrcInfos GdExp where
    collectSrcInfos (GdExp s g e) = [s] ++ (collectSrcInfos g) ++ (collectSrcInfos e)

instance CollectSrcInfos Lit where
    collectSrcInfos (IntegerLit s _ _) = [s]
    collectSrcInfos (FloatLit s _ _ _) = [s]
    collectSrcInfos (CharLit  s _)   = [s]
    collectSrcInfos (StrLit   s _)   = [s]

instance CollectSrcInfos Sig where
    collectSrcInfos (Sig id at tschm) = 
	(collectSrcInfos id) ++
	(collectSrcInfos at) ++
        (collectSrcInfos tschm)

instance CollectSrcInfos TSchm where
    collectSrcInfos (TSchm ctxt ty) = (collectSrcInfos ctxt) ++ (collectSrcInfos ty)

instance CollectSrcInfos AnnType where
    collectSrcInfos _ = []

instance CollectSrcInfos Data where
    collectSrcInfos (Data id ids cons deriv) =
	(collectSrcInfos (id:ids))++
	(collectSrcInfos cons) ++
	(collectSrcInfos deriv)

instance CollectSrcInfos Deriv where
    collectSrcInfos (Deriv ids) = collectSrcInfos ids

instance CollectSrcInfos Con where
    collectSrcInfos (Con id tys) = (collectSrcInfos id) ++ (collectSrcInfos tys)
    collectSrcInfos (QCon ids cnst id ty) =
	(collectSrcInfos ids) ++
	(collectSrcInfos cnst) ++
	(collectSrcInfos id) ++
	(collectSrcInfos ty)
    collectSrcInfos (RecCon id fdefs) = (collectSrcInfos id) ++ (collectSrcInfos fdefs)
    collectSrcInfos (RecQCon ids cnst id fdefs) = 
	(collectSrcInfos ids) ++
	(collectSrcInfos cnst) ++ 
	(collectSrcInfos id) ++
	(collectSrcInfos fdefs)

instance CollectSrcInfos FieldDef where
    collectSrcInfos (FieldDef id ty) = (collectSrcInfos id) ++ (collectSrcInfos ty)

instance CollectSrcInfos RHS where
    collectSrcInfos (RHS1 e) = collectSrcInfos e
    collectSrcInfos (RHSG gdexps) = collectSrcInfos gdexps

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

emptyCtxt :: Ctxt
emptyCtxt = Ctxt []

emptyCnst :: Cnst
emptyCnst = Cnst []

addCtxt :: Ctxt -> Ctxt -> Ctxt
addCtxt (Ctxt ps1) (Ctxt ps2) = Ctxt (ps1 ++ ps2)

addCnst :: Cnst -> Cnst -> Cnst
addCnst (Cnst cs1) (Cnst cs2) = Cnst (cs1 ++ cs2)

-- adds existential variables to a Con
addExistVarsCon :: [Id] -> Con -> Con
addExistVarsCon vs (Con id ts) = QCon vs emptyCnst id ts
addExistVarsCon vs (QCon vs' cnst id ts) = QCon (vs++vs') cnst id ts
addExistVarsCon vs (RecCon id fs) = RecQCon vs emptyCnst id fs
addExistVarsCon vs (RecQCon vs' cnst id fs) = RecQCon (vs++vs') cnst id fs

-- adds to the context of the given Con 
addCnstCon :: Cnst -> Con -> Con
addCnstCon cnst (Con id ts)	      = QCon [] cnst id ts
addCnstCon cnst (QCon vs cnst' id ts) = QCon vs (cnst `addCnst` cnst') id ts
addCnstCon cnst (RecCon id fs)	      = RecQCon [] cnst id fs
addCnstCon cnst (RecQCon vs cnst' id fs) = RecQCon vs (cnst`addCnst`cnst') id fs

-- true for record-style constructors
isRecCon :: Con -> Bool
isRecCon (RecCon _ _) = True
isRecCon (RecQCon _ _ _ _) = True
isRecCon _ = False

-- merges neighbouring Defs with the same name into a single Def.
-- returns all other declarations untouched
mergeDefs :: [Dec] -> [Dec]
mergeDefs ds = merge ds
  where
    merge [] = []
    merge (d:ds) | isValDec d = let id = valDecIdStr d
				    (ds1,ds2) = span (isValDec &&& 
						     ((==id).valDecIdStr)) ds
				in  addDefs d (concatMap defs ds1) : merge ds2
		 | otherwise  = d : merge ds

    isValDec (ValDec _ _) = True
    isValDec _ = False
    
    valDecIdStr (ValDec _ (Def id _ _ _:_)) = idStr id
    defs (ValDec _ fs) = fs
    addDefs (ValDec s fs') fs = ValDec s (fs'++fs)


dropAnnDecs :: [Dec] -> [Dec]
dropAnnDecs = filter (not . isAnnDec) 

isAnnDec (AnnDec _ _) = True
isAnnDec _ = False

-- looks for an Ann Dec with matching id
findAnn :: Id -> [Dec] -> Maybe Dec
findAnn id ds = listToMaybe [ d | d@(AnnDec s (Sig sid _ _)) <- ds, sid == id ]

defsId :: [Def] -> Id
defsId (Def id _ _ _:_) = id

--------------------------------------------------------------------------------

-- Applies an expression transforming function to each sub-expression in the
-- program in a top-down function. (i.e. transforms an expression, then all
-- children of that new expression.)

appExpProg :: (Exp -> Exp) -> Prog -> Prog
appExpProg f (Prog ms) = Prog (map (appExpModule f) ms)

appExpModule :: (Exp -> Exp) -> Module -> Module
appExpModule f (Module id ims exs ds modtype) = 
		Module id ims exs (map (appExpDec f) ds) modtype
{- for x-modules
appExpModule f (Xmodule id ims exs ds) = 
		Xmodule id ims exs (map (appExpDec f) ds)
-}

appExpDec :: (Exp -> Exp) -> Dec -> Dec
appExpDec f dec = case dec of
    ValDec s ds  -> ValDec s (map (appExpDef f) ds)
    PatDec s pb  -> PatDec s (appExpPatBnd f pb)
    ClassDec s c -> ClassDec s (appExpClass f c)
    InstDec s i  -> InstDec s (appExpInst f i)
    d		 -> d

appExpClass :: (Exp -> Exp) -> Class -> Class
appExpClass f (Class c p fds w) = Class c p fds (chDecs f w)

appExpInst  :: (Exp -> Exp) -> Inst -> Inst
appExpInst f (Inst c p w) = Inst c p (chDecs f w)

appExpPatBnd :: (Exp -> Exp) -> PatBnd -> PatBnd
appExpPatBnd f (PatBnd p rhs w) = PatBnd p (chRHS f rhs) (chDecs f w)

-- apply the given function to the top-level expression in the def
appExpDef :: (Exp -> Exp) -> Def -> Def
appExpDef f def = chDef f def

chDefs f ds = map (chDef f) ds
chDef  f (Def id ps rhs w) = Def id ps (chRHS f rhs) (chDecs f w)

chRHS f (RHS1 ae)  = RHS1 (chExp f ae)
chRHS f (RHSG ges) = RHSG (map (chGdExp f) ges)

chDecs :: (Exp -> Exp) -> [Dec] -> [Dec]
chDecs f = map (chDec f) 
chDec = appExpDec

chStmt f stmt = case stmt of
    GenStmt s p e -> GenStmt s p (chExp f e)
    QualStmt s e  -> QualStmt s (chExp f e)
    LetStmt s ds  -> LetStmt s (chDecs f ds)

chAlt f (CaseAlt s p e w)     = CaseAlt s p (chRHS f e) (chDecs f w)

chGdExp f (GdExp s g e) = GdExp s (chExp f g) (chExp f e)

chExp f exp = case f exp of
    NegExp s e	    -> NegExp s (chx e)
    AbsExp s id e1  -> AbsExp s id (chx e1)
    AppExp s e1 e2  -> AppExp s (chx e1) (chx e2)
    IfxAppExp  s e1 e2 e3 -> IfxAppExp  s (chx e1) (chx e2) (chx e3)
    PIfxAppExp s e1 e2 e3 -> PIfxAppExp s (chx e1) (chx e2) (chx e3)
    IfExp s1 e1 s2 e2 e3  -> IfExp s1 (chx e1) s2 (chx e2) (chx e3)
    AnnExp s e at ts -> AnnExp s (chx e) at ts
    TupExp s es	  -> TupExp s (map chx es)
    LetExp s ds e -> LetExp s (chDecs f ds) (chx e)
    DoExp  s ss   -> DoExp s (map (chStmt f) ss)
    CaseExp s e as-> CaseExp s (chx e) (map (chAlt f) as)
    ListExp s1 (Many s2 es) -> ListExp s1 (Many s2 (map chx es))
    ListCompExp s e ss  -> ListCompExp s (chx e) (map (chStmt f) ss)
    SecLeftExp  s e1 e2 -> SecLeftExp  s (chx e1) (chx e2)
    SecRightExp s e1 e2 -> SecRightExp s (chx e1) (chx e2)
    EnumFromExp s e1    -> EnumFromExp s (chx e1)
    EnumFromToExp s e1 e2   -> EnumFromToExp s (chx e1) (chx e2)
    EnumFromThenExp s e1 e2 -> EnumFromThenExp s (chx e1) (chx e2)
    EnumFromThenToExp s e1 e2 e3 -> EnumFromThenToExp s (chx e1)
					 (chx e2) (chx e3)
    e -> e	-- no subexpressions
  where
    chx = chExp f


--------------------------------------------------------------------------------



{-------------------------------------------------------------------------------
NOTE: Below are a bunch of functions which were used in the original Chameleon
      system. These are examples of simple boilerplate style traversal code,
      but none of them is of any direct use in this new module.

-------------------------------------------------------------------------------}
{-------------------------------------------------------------------------------
--------------------------------------------------------------------------------


nullCtxt (Ctxt ps) = null ps
emptyCtxt = Ctxt []
sigPreds (Sig _ _ ctxt _) = case item ctxt of Ctxt aps -> aps
firstCtxtPred (Ctxt aps) = heady "firstCtxtPred" aps

rhsExps (RHS1 e)   = [e]
rhsExps (RHSG ges) = let (gs, es) = unzip ges in gs ++ es

isUnivSig (Sig st _ _ _) = st == Univ
univSig  = Sig Univ
existSig = Sig Exist

tschmToSig (TSchm c t) id = Sig Univ id c t
makeSigUniv  (Sig _ id c t) = Sig Univ id c t
makeSigExist (Sig _ id c t) = Sig Exist id c t

sigAnnType (Sig at _ _ _) = at

patAVars :: Ann Pat -> [Ann Id]
patAVars ap = case item ap of
    VarPat id -> [Ann (ann ap) id]
    ConPat _ ps -> concatMap patAVars ps
    TupPat ps   -> concatMap patAVars ps
    ListPat ps  -> concatMap patAVars ps
    _ -> []

-- given a pattern variable, and a pattern, replaces all other variables in the
-- pattern by 'don't-cares'
replaceOtherPatVars :: Id -> Ann Pat -> Ann Pat
replaceOtherPatVars v ap = Ann (ann ap) $ case item ap of
      p@(VarPat id) | v == id   -> p
  		    | otherwise	-> JokPat
      ConPat id ps-> ConPat id (map (replaceOtherPatVars v) ps)
      TupPat ps   -> TupPat (map (replaceOtherPatVars v) ps)
      ListPat ps  -> ListPat (map (replaceOtherPatVars v) ps)
      p -> p

-- These are meaningless declarations which delimit the non-local declarations 
-- in the program, separating them from the imports for display purposes.
nonlocalDecStart :: Ann Dec
nonlocalDecStart= Ann (unkIx (-4)) (InterfaceDec (Ann noIx nonlocalDecStartStr))
nonlocalDecEnd  = Ann (unkIx (-4)) (InterfaceDec (Ann noIx nonlocalDecEndStr))

nonlocalDecStartStr = "-- START NON-LOCAL DECS --"
nonlocalDecEndStr   = "-- END NON-LOCAL DECS --"

-- strips out all declarations bracketed by the above delimiters
dropNonlocalDecs :: [Ann Dec] -> [Ann Dec]
dropNonlocalDecs ads = skip 0 ads
  where
    skip _ [] = []
    skip n (Ann _ (InterfaceDec (Ann _ str)):ads) 
	| str == nonlocalDecStartStr = skip (n+1) ads
	| str == nonlocalDecEndStr   = skip (n-1) ads
    skip 0 (ad:ads) = ad : skip 0 ads
    skip n (ad:ads) = skip n ads

--------------------------------------------------------------------------------
-- strips all annotations from the program

strip :: Prog -> I.Prog
strip = stProg

stProg (Prog decs)	= I.Prog (concatMap stDec (map item decs))

stId  a 		= a

stDec (DatDec  a)	= [I.DatDec  (stDat  (item a))]
stDec (ValDec a)	= [I.ValDec (map stDef (items a))]
stDec (AValDec a b)	= if isUnivSig (item a)
			  then [I.AValDec(stSig (item a)) (map stDef (items b))]
			  else [I.ValDec (map stDef (items b))]
stDec (InterfaceDec a) | item a /= nonlocalDecStartStr && 
			 item a /= nonlocalDecEndStr = [I.ImportDec (item a)]
		       | otherwise = []
stDec (PatDec a b c)	= [I.PatDec (stPat (item a)) (stRHS (item b))
				    (concatMap (stDec . item) c)]
-- other declarations have no Haskell equivalent and should be left out
stDec _ = []	    

stDat (Dat a b c)	= I.Dat (stId (item a)) (map stId (items b))
				(map stCon (items c))

stCon (Con a b)		= I.Con (stId (item a)) (map stTyp (items b))

stDef (Def a b c d)	= I.Def (stId (item a)) (map stPat (items b)) 
				(stRHS (item c)) (concatMap (stDec . item) d)

stRHS (RHS1 a)		= I.RHS1 (stExp (item a))
stRHS (RHSG a)		= I.RHSG (map (\(g,e) -> (stExp (item g), 
						  stExp (item e))) a)

stExp :: Exp -> I.Exp
stExp (VarExp a)	= I.VarExp (stId a)
stExp (ConExp a)	= I.ConExp (stId a)
stExp (LitExp a)	= I.LitExp (stLit a)
stExp (NegExp a)	= I.NegExp (stExp (item a))
stExp (AbsExp a b)	= I.AbsExp (map stPat (items a)) (stExp (item b))
stExp (AppExp a b)	= I.AppExp (stExp (item a)) (stExp (item b))
stExp (IfxAppExp a b c)	= I.IfxAppExp (stExp (item a)) (stExp (item b))
				      (stExp (item c))
stExp (LetExp a b)	= I.LetExp (concatMap (stDec .item) a) (stExp (item b)) 
stExp (DoExp a)		= I.DoExp (map stStmt (items a))
stExp (CaseExp a b)	= I.CaseExp (stExp (item a)) (map stAlt b)
stExp (IfExp  a b c)	= I.IfExp  (stExp (item (item a))) (stExp (item b)) 
				   (stExp (item c))
stExp (AnnExp a b)	= I.AnnExp (stExp (item a)) (stTSchm (item b))
stExp (TAddExp a b)	= stExp (item a)
stExp (TupExp a)	= I.TupExp (map stExp (items a))
stExp (ListExp a)	= I.ListExp (map stExp (items (item a)))

stExp (ListCompExp a b)	= I.ListCompExp (stExp (item a)) (map stStmt (items b))

stExp (SecExpLeft  a b)	= I.SecExpLeft  (stExp (item a)) (stExp (item b))
stExp (SecExpRight a b)	= I.SecExpRight (stExp (item a)) (stExp (item b))

stExp (EnumExpFrom e1)  = I.EnumExpFrom (stExp (item e1))
stExp (EnumExpFromTo e1 e2) = I.EnumExpFromTo (stExp(item e1)) (stExp(item e2))
stExp (EnumExpFromThen e1 e2) = I.EnumExpFromThen (stExp(item e1)) 
						  (stExp(item e2))
stExp (EnumExpFromThenTo e1 e2 e3) = I.EnumExpFromThenTo (stExp(item e1))
					    (stExp(item e2)) (stExp(item e3))					    

stStmt (GenStmt a b)	= I.GenStmt (stPat (item a)) (stExp (item b))
stStmt (QualStmt a)	= I.QualStmt (stExp (item a))
stStmt (LetStmt ds)	= I.LetStmt (concatMap stDec (items ds))

stAlt (CaseAlt a b c)	   = I.CaseAlt (stPat (item a)) (stExp (item b))
				       (concatMap stDec (items c))
stAlt (CaseAltGuard a b c) = I.CaseAltGuard (stPat (item a)) (map stGdExp b)
					    (concatMap stDec (items c))

stGdExp (g, e) = (stExp (item g), stExp (item e))

stLit (IntLit  a b)	= I.IntLit a
stLit (FloatLit a b)	= I.FloatLit a
stLit (StrLit  a)	= I.StrLit a
stLit (CharLit a)	= I.CharLit a

stPat (JokPat)		= I.JokPat
stPat (VarPat a)	= I.VarPat (stId a)
stPat (LitPat a)	= I.LitPat (stLit a)
stPat (ConPat a b)	= I.ConPat (stId (item a)) (map stPat (items b))
stPat (TupPat a)	= I.TupPat (map stPat (items a))
stPat (ListPat a)	= I.ListPat (map stPat (items a))

stSig (Sig _ a b c)	= I.Sig (stId (item a)) (stCtxt (item b)) 
				(stTyp (item c))				

stTSchm (TSchm a b)	= I.TSchm (stCtxt (item a)) (stTyp (item b))

stTyp (VarTyp a)	= I.VarTyp (stId a)
stTyp (ConTyp a)	= I.ConTyp (stId a)
stTyp (AppTyp a b)	= I.AppTyp (stTyp (item a)) (stTyp (item b))
stTyp (TupTyp a)	= I.TupTyp (map stTyp (items a))
stTyp (ListTyp a)	= I.ListTyp (stTyp (item a))

stCtxt (Ctxt a)		= map stPred (items a)
stCnst (Cnst a)		= map stPrim (items a)

stRule (PropRule a b)	= I.PropRule (stCtxt (item a)) (stCnst (item b))
stRule (SimpRule a b)	= I.SimpRule (stCtxt (item a)) (stCnst (item b))

stPred (Pred a b)	= I.Pred (stId a) (stTyp (item b))
stPrim (PredPrim a)	= I.PredPrim (stPred (item a))
stPrim (EqPrim a b)	= I.EqPrim (stTyp (item a)) (stTyp (item b))
 


--------------------------------------------------------------------------------

-- relabels stuff, also keeps track of the mapping from old to new labels
newtype Relabeler a = Relabeler ((Loc, RelabelMap) -> ((Loc, RelabelMap), a))

-- relates old location numbers to new location numbers
type RelabelMap = [(Loc, Loc)]

instance Monad Relabeler where
    -- return :: a -> RState a
    return a = Relabeler (\l -> (l, a))

    -- (>>=) :: Relabeler a -> (a -> Relabeler b) -> Relabeler b
    (Relabeler f) >>= g = Relabeler (\l -> let (l',a) = f $! l
					       Relabeler e = g $! a
					   in  e $! l')

-- runs a relabeler, returning the relabeled result
runRelabeler (Relabeler f) = snd (f (1,[]))
runRelabelerFrom n (Relabeler f) = snd (f (n,[]))

-- relabels as above, but also returns a mapping from old to new labels
runRelabelerMap :: Relabeler a -> (a, RelabelMap)
runRelabelerMap (Relabeler f) = let ((_,m), r) = f (1, [])
				in  (r, m)

-- returns the current label, and updates the internal state
nextLabel :: Relabeler Loc
nextLabel = Relabeler (\(l,r) -> ((l+1, r), l))
 
extendLabelMap :: (Loc, Loc) -> Relabeler ()
extendLabelMap ls = Relabeler (\(l,r) -> ((l,ls:r), ()))

 
relabel :: Ann a -> Relabeler (Ann a)
relabel ax@(Ann ix a) = case ix of
    Ix _ f s -> do l <- nextLabel
		   let ix' = Ix l f s
		   return (Ann ix' a)
    NoIx     -> return ax


newlabel :: Index -> Relabeler (a -> Ann a)
newlabel NoIx       = return (\a -> Ann NoIx a)
newlabel (Ix l f s) = do l' <- nextLabel 
			 extendLabelMap (l,l')
			 return (\a -> Ann (Ix l' f s) a)

relabelMany :: [Ann a] -> Relabeler [Ann a]
relabelMany = mapM relabel

f |>  m = f >>= \g -> m >>= \r -> return (g $! r) 
f ||> m = m >>= \r -> return (f $! r)


-- changes all the program's annotations 
-- (only useful for the very first program read, since the relabeling starts 
--  from 1)
relabelInitProg :: Prog -> Prog
relabelInitProg p = runRelabeler (relabelProg p)

-- relabels the given program (assumed to be freshly parsed), and returns a
-- mapping from the old locations to new
relabelInitProgMap :: Prog -> (Prog, RelabelMap)
relabelInitProgMap p = runRelabelerMap (relabelProg p)
		       -- (relabelInitProg p, zip [1..] [1..])

-- as above, but the first location number must be specified
relabelProgFrom :: Int -> Prog -> Prog
relabelProgFrom n p = runRelabelerFrom n (relabelProg p)

-- renumbers the locations of all locations in the program such that lower
-- numbers belong to "higher" locations (in the tree)
-- NOTE: source location info. is retained
relabelProg :: Prog -> Relabeler Prog
relabelProg (Prog ads) = Prog ||> mapM relabelDec ads


relabelDec :: Ann Dec -> Relabeler (Ann Dec)
relabelDec (Ann ix ad) = newlabel ix |> case ad of
    ValDec ads     -> ValDec ||> mapM relabelDef ads
    AValDec as ads -> AValDec ||> relabelSig as |> mapM relabelDef ads
    OverDec as ads -> OverDec ||> relabelSig as |> mapM relabelDef ads
    RuleDec ar     -> RuleDec ||> relabelRule ar
    PatDec ap rhs w  -> PatDec ||> relabelPat ap |> relabelRHS rhs |> 
				   relabelWhere w
    InterfaceDec aid -> InterfaceDec ||> relabelBase aid
    InstDec ais ads  -> InstDec ||> relabelInstSig ais |> mapM relabelDef ads
    ExternDec (Left  as)  -> ExternDec ||> (Left  ||> relabelSig as)
    ExternDec (Right aid) -> ExternDec ||> (Right ||> relabelBase aid)
    _		   -> return ad


relabelSig (Ann ix (Sig t aid ac at)) = newlabel ix |>
    (Sig t ||> relabelBase aid |> relabelCtxt ac |> relabelTyp at)

relabelInstSig (Ann ix (InstSig ac ap)) = newlabel ix |>
    (InstSig ||> relabelCtxt ac |> relabelPred ap)

relabelTSchm (Ann ix (TSchm ac at)) = newlabel ix |>
    (TSchm ||> relabelCtxt ac |> relabelTyp at)

relabelRule (Ann ix ar) = newlabel ix |> case ar of
    PropRule actxt acnst -> PropRule ||> relabelCtxt actxt |> relabelCnst acnst
    SimpRule actxt acnst -> SimpRule ||> relabelCtxt actxt |> relabelCnst acnst

relabelCtxt (Ann ix (Ctxt aps)) = newlabel ix |> (Ctxt ||> mapM relabelPred aps)
relabelCnst (Ann ix (Cnst aps)) = newlabel ix |> (Cnst ||> mapM relabelPrim aps)
relabelPred (Ann ix (Pred id at)) = newlabel ix |> (Pred id ||> relabelTyp at)
relabelPrim (Ann ix p) = newlabel ix |> case p of
    PredPrim ap	     -> PredPrim ||> relabelPred ap
    EqPrim   at1 at2 -> EqPrim   ||> relabelTyp at1 |> relabelTyp at2
    

relabelTyp (Ann ix at) = newlabel ix |> case at of
    AppTyp at1 at2 -> AppTyp ||> relabelTyp at1 |> relabelTyp at2
    TupTyp ats	   -> TupTyp ||> mapM relabelTyp ats
    ListTyp at	   -> ListTyp ||> relabelTyp at
    _ -> return at


relabelDef :: Ann Def -> Relabeler (Ann Def)
relabelDef (Ann ix (Def aid aps rhs w)) = do
    new <- newlabel ix
    r_ps  <- mapM relabelPat aps
    r_id  <- relabelBase aid
    r_rhs <- relabelRHS rhs
    new ||> (Def ||> return r_id |> return r_ps
		 |> return r_rhs |> relabelWhere w)


{-    
relabelDef (Ann ix (Def aid aps rhs w)) = do
    newlabel ix |>
	(Def ||> relabelBase aid |> mapM relabelPat aps 
	     |> relabelRHS rhs   |> relabelWhere w)
-}

relabelBase (Ann ix x) = newlabel ix |> return x


relabelPat (Ann ix (ConPat aid aps)) = newlabel ix |>
	    (ConPat ||> relabelBase aid |> mapM relabelPat aps)
relabelPat (Ann ix (TupPat aps)) = newlabel ix |> 
	    (TupPat ||> mapM relabelPat aps)
relabelPat (Ann ix (ListPat aps)) = newlabel ix |>
	    (ListPat ||> mapM relabelPat aps)
relabelPat p = relabelBase p


relabelRHS (Ann ix (RHS1 ae))  = newlabel ix |> (RHS1 ||> relabelExp ae)
relabelRHS (Ann ix (RHSG ges)) = 
		    newlabel ix |> (RHSG ||> mapM relabelGuardedExp ges)


relabelGuardedExp (ag, ae) = (,) ||> relabelExp ag |> relabelExp ae


relabelWhere = mapM relabelDec 

relabelExp (Ann ix e) = newlabel ix |> case e of
    AbsExp aps ae  -> AbsExp ||> mapM relabelPat aps |> relabelExp ae
    AppExp ae1 ae2 -> AppExp ||> relabelExp ae1 |> relabelExp ae2
    IfxAppExp ae1 ae2 ae3 -> IfxAppExp ||> relabelExp ae1 |> relabelExp ae2 |>
					   relabelExp ae3
    PIfxAppExp ae1 ae2 ae3 -> PIfxAppExp ||> relabelExp ae1 |> relabelExp ae2 |>
					     relabelExp ae3
    LetExp ads ae  -> LetExp ||> mapM relabelDec ads |> relabelExp ae
    TupExp aes   -> TupExp  ||> mapM relabelExp aes
    IfExp aae1 ae2 ae3 -> do Ann ix ae1 <- relabelBase aae1
			     ae1' <- relabelExp ae1
			     ae2' <- relabelExp ae2
			     ae3' <- relabelExp ae3
			     return (IfExp (Ann ix ae1') ae2' ae3')
    ListExp aaes -> ListExp ||> do Ann ix aes <- relabelBase aaes 
				   aes' <- mapM relabelExp aes
				   return (Ann ix aes')
    SecExpLeft  ae1 ae2 -> SecExpLeft  ||> relabelExp ae1 |> relabelExp ae2
    SecExpRight ae1 ae2 -> SecExpRight ||> relabelExp ae1 |> relabelExp ae2
    EnumExpFrom ae1 -> EnumExpFrom ||> relabelExp ae1
    EnumExpFromTo   ae1 ae2 -> EnumExpFromTo ||> relabelExp ae1 |> 
						 relabelExp ae2
    EnumExpFromThen ae1 ae2 -> EnumExpFromThen ||> relabelExp ae1 |> 
						   relabelExp ae2
    EnumExpFromThenTo ae1 ae2 ae3 -> EnumExpFromThenTo ||> relabelExp ae1 |>
					 relabelExp ae2 |> relabelExp ae3

    TAddExp ae at -> TAddExp ||> relabelExp ae |> relabelTSchm at
    AnnExp  ae at -> AnnExp  ||> relabelExp ae |> relabelTSchm at
    DoExp   ass -> DoExp ||> mapM relabelStmt ass
    CaseExp ae cas -> CaseExp ||> relabelExp ae |> mapM relabelCaseAlt cas
    ListCompExp ae ass -> ListCompExp ||> relabelExp ae |> mapM relabelStmt ass
    _		    -> return e

relabelStmt (Ann ix stmt) = newlabel ix |> case stmt of
    GenStmt ap ae -> GenStmt ||> relabelPat ap |> relabelExp ae
    QualStmt ae   -> QualStmt ||> relabelExp ae
    LetStmt  ads  -> LetStmt ||> mapM relabelDec ads

relabelCaseAlt (CaseAlt ap ae w) = 
	CaseAlt ||> relabelPat ap |> relabelExp ae |> relabelWhere w
relabelCaseAlt (CaseAltGuard ap ges w) = 
	CaseAltGuard ||> relabelPat ap |> mapM relabelGuardedExp ges |> 
			 relabelWhere w
					

--------------------------------------------------------------------------------

appExpProg :: (Ann Exp -> Ann Exp) -> Prog -> Prog
appExpProg f (Prog ads) = Prog (map (appExpDec f) ads)

appExpDec :: (Ann Exp -> Ann Exp) -> Ann Dec -> Ann Dec
appExpDec f adec = 
    let ix  = ann adec
	dec = item adec
    in  Ann ix $ case dec of
		    ValDec ads	  -> ValDec (map (appExpDef f) ads)
		    AValDec s ads -> AValDec s (map (appExpDef f) ads)
		    OverDec s ads -> OverDec s (map (appExpDef f) ads)
		    InstDec s ads -> InstDec s (map (appExpDef f) ads)
		    PatDec p rhs w-> PatDec p (chRHS f rhs) (chDecs f w)
		    d		  -> d

-- apply the given function to the top-level expression in the def
appExpDef :: (Ann Exp -> Ann Exp) -> Ann Def -> Ann Def
appExpDef f def = chDef f def
	
chRHS f (Ann ix (RHS1 ae))  = Ann ix (RHS1 (chExp f ae))
chRHS f (Ann ix (RHSG ges)) = 
		    Ann ix (RHSG [ (chExp f g, chExp f e) | (g,e) <- ges ])


-- why not call appExpDec above?
chDecs :: (Ann Exp -> Ann Exp) -> [Ann Dec] -> [Ann Dec]
chDecs f ads = map (chDec f) ads
chDec = appExpDec

		
chDefs f ads = map (chDef f) ads
chDef  f ad  = 
	     let d  = item ad 
		 ix = ann ad
	     in  case d of
		Def id ps rhs w -> Ann ix (Def id ps (chRHS f rhs)
						     (chDecs f w))
chStmt f stmt = let ix = ann stmt
	        in  Ann ix $ case item stmt of
    GenStmt p e -> GenStmt p (chExp f e)
    QualStmt e  -> QualStmt (chExp f e)
    LetStmt ds  -> LetStmt (chDecs f ds)

chAlt f (CaseAlt p e w) = CaseAlt p (chExp f e) (chDecs f w)
chAlt f (CaseAltGuard p ges w) = CaseAltGuard p (map chGE ges) (chDecs f w)
    where chGE (g,e) = (chExp f g, chExp f e)

chExp f aexp = let aexp' = f aexp
		   chExp' = chExp f
	       in  Ann (ann aexp') $ case item aexp' of
    
    NegExp e -> NegExp (chExp' e)
    AbsExp id e1  -> AbsExp id (chExp' e1)
    AppExp e1 e2  -> AppExp (chExp' e1) (chExp' e2)
    IfxAppExp  e1 e2 e3 -> IfxAppExp  (chExp' e1) (chExp' e2) (chExp' e3)
    PIfxAppExp e1 e2 e3 -> PIfxAppExp (chExp' e1) (chExp' e2) (chExp' e3)
    IfExp  e1 e2 e3 -> IfExp (chExp' (item e1) `withAnnOf` e1) 
			     (chExp' e2) (chExp' e3)
    AnnExp e1 t	  -> AnnExp (chExp' e1) t
    TupExp es	  -> TupExp (map chExp' es)
    LetExp ds e1  -> LetExp (chDecs f ds) (chExp' e1)
    DoExp  ss     -> DoExp (map (chStmt f) ss)
    CaseExp e as  -> CaseExp (chExp' e) (map (chAlt f) as)
    ListExp aes	     -> ListExp (map chExp' (item aes) `withAnnOf` aes)
    ListCompExp e ss -> ListCompExp (chExp' e) (map (chStmt f) ss)
    SecExpLeft  e1 e2 -> SecExpLeft  (chExp' e1) (chExp' e2)
    SecExpRight e1 e2 -> SecExpRight (chExp' e1) (chExp' e2)
    EnumExpFrom e1 -> EnumExpFrom (chExp' e1)
    EnumExpFromTo e1 e2	-> EnumExpFromTo (chExp' e1) (chExp' e2)
    EnumExpFromThen e1 e2 -> EnumExpFromThen (chExp' e1) (chExp' e2)
    EnumExpFromThenTo e1 e2 e3 -> EnumExpFromThenTo (chExp' e1)
					 (chExp' e2) (chExp' e3)
    e -> e	-- no subexpressions



--------------------------------------------------------------------------------
-- source-based debugger commands

data SrcCommand = SCTypeLoc Loc		    -- type command
		| SCTypeVar Id Loc
		| SCExplainLoc Loc TSchm    -- explain command
		| SCExplainVar Id Loc TSchm

instance Show SrcCommand where 
    show (SCTypeLoc l)	      = "SCTypeLoc " ++ show l
    show (SCTypeVar i l)      = "SCTypeVar " ++ show (i, l)
    show (SCExplainLoc l t)   = "SCExplainLoc " ++ show l
    show (SCExplainVar i l t) = "SCExplainVar " ++ show (i, l)

relabelSrcCommands :: RelabelMap -> [SrcCommand] -> [SrcCommand]
relabelSrcCommands m = map (relabelSrcCommand m)

relabelSrcCommand :: RelabelMap -> SrcCommand -> SrcCommand
relabelSrcCommand m sc = case sc of
    SCTypeLoc l		 -> SCTypeLoc (rel l)
    SCTypeVar id l	 -> SCTypeVar id (rel l)
    SCExplainLoc l ts    -> SCExplainLoc (rel l) ts
    SCExplainVar id l ts -> SCExplainVar id (rel l) ts
  where
    rel l = case lookup l m of
	     Nothing -> trace ("BUG: no relabelling for location " ++ show l) l
	     Just l' -> l'
--------------------------------------------------------------------------------
-------------------------------------------------------------------------------}

instance Pretty Prog where
    pretty (Prog ms) = prettyLines ms

instance Pretty Module where
    pretty (Module id xs is ds ty) = "module " ++ pretty id ++ " " ++ 
				  pretty xs ++ "\n" ++ prettyLines is ++ "\n" ++
				  pretty ds  ++ "\n" ++ pretty ty

instance Pretty ModType where
    pretty Xmod = ""
    pretty Cmod = ""

instance Pretty Dec where
    pretty (RuleDec  _ rule)     = pretty rule
    pretty (DataDec  _ data_)    = pretty data_
    pretty (TypeDec  _ tsyn)     = pretty tsyn
    pretty (AnnDec   _ sig)      = pretty sig
    pretty (ExtDec   _ extern)   = pretty extern
    pretty (ValDec   _ defs)     = pretty defs
    pretty (PatDec   _ patbnd)   = pretty patbnd
    pretty (OverDec  _ over)     = pretty over
    pretty (ClassDec _ class_)   = pretty class_
    pretty (InstDec  _ inst)     = pretty inst
    pretty (FixDec   _ fixity)   = pretty fixity
    pretty (PrimDec  _ primval)  = pretty primval
    pretty (ConsDec  _ constr)   = pretty constr
    pretty (ExtConsDec _ pred)  = "constraint " ++ (pretty pred)
    prettySep _			 = "\n"

instance Pretty Constr where
    pretty (ConstrCls id ty)  = "constraint " ++ (pretty id) ++ " :: " ++ (pretty ty)
    pretty (ConstrData id ty) = "constraint " ++ (pretty id) ++ " :: " ++ (pretty ty)

instance Pretty Rule where
    pretty (PropRule ctxt cnst)  = "rule (" ++ (pretty ctxt) ++ ")" ++ "==>" ++ (pretty cnst)
    pretty (SimpRule ctxt cnst)  = "rule (" ++ (pretty ctxt) ++ ")" ++ "<==>" ++ (pretty cnst)

instance Pretty Data where
    pretty (Data id ids cons deriv) = "data " ++ (pretty id) ++ (pretty ids) ++ " = " ++ (pretty cons) ++ (pretty deriv)
    pretty (DataKindAnn id ts cons deriv) = "data " ++ (pretty id) ++ (pretty ts) ++ " = " ++ (pretty cons) ++ (pretty deriv)

instance Pretty Con where
    pretty (Con id types)		= "(" ++ (pretty id) ++ " " ++ (pretty types) ++ ")"
    pretty (QCon ids cnst id types)	= "(Forall " ++ (pretty ids) ++ (pretty cnst) ++ (pretty id) ++ (pretty types) ++ ")"
    pretty (RecCon id fds)		= (pretty id) ++ " { " ++ (pretty fds) ++ " } "
    pretty (RecQCon ids cnst id fds)	= "(Forall " ++ (pretty ids) ++ (pretty cnst) ++ (pretty id) ++ " { " ++ (pretty fds) ++ ")"
    prettySep _ = " | "

instance Pretty Type where
    pretty (VarType id)		= pretty id
    pretty (ConType id)		= pretty id
    pretty (ArrType _ ty1 ty2)	= "(" ++ (pretty ty1) ++ "->" ++ (pretty ty2) ++ ")"
    pretty (AppType _ ty1 ty2)  = "(" ++ (pretty ty1) ++ " " ++ (pretty ty2) ++ ")"
    pretty (TupType _ types)	= "(" ++ (pretty types) ++ ",)"
    pretty (ListType _ t)	= "[" ++ (pretty t) ++ "]"
    pretty (UnionType _ types)  = "(" ++ (pretty types) ++ "|)"
    pretty (StarType _ t)	= "(" ++ (pretty t) ++ "*)"
    pretty (OptionType _ t)	= "(" ++ (pretty t) ++ "?)"
    pretty (AnnType _ id t)     = "(" ++ (pretty id) ++ " :: " ++ (pretty t) ++ ")"
    pretty (FuncType _ id ts)   = "(" ++ (pretty id) ++ " " ++ (pretty ts) ++ ")"
    prettySep _ = " "

instance Pretty FieldDef where
    pretty (FieldDef id ty)	= (pretty id) ++ " :: " ++ (pretty ty)
    prettySep _ = " "

instance Pretty Deriv where
    pretty (Deriv ids)		= " deriving ("++ (pretty ids) ++ ")"

instance Pretty TSyn where
    pretty (TSyn id ids ty)	= "type " ++ (pretty id) ++ (pretty ids) ++ " = " ++ (pretty ty)

instance Pretty Sig where
    pretty (Sig id at ts)	= (pretty id) ++ (pretty at) ++ (pretty ts)

instance Pretty AnnType where
    pretty Univ			= " :: "
    pretty Exist		= " ::: "
    pretty Reg			= " :*: "

instance Pretty TSchm where
    pretty (TSchm ctxt ty)	= " ( " ++ (pretty ctxt) ++ " ) => " ++ (pretty ty)

instance Pretty Extern where
    pretty (VarExt sig)		= "extern " ++ (pretty sig)
    pretty (TConExt id)		= "extern " ++ (pretty id)

instance Pretty Def where
    pretty (Def id pats rhs wh)	= (pretty id) ++ "(" ++ (pretty pats) ++ ")" ++ (pretty rhs) ++ "\n where \n" ++ (pretty wh)

instance Pretty Pat where
    pretty (VarPat id)		= (pretty id)
    pretty (LitPat lit)		= pretty lit
    pretty (AsPat _ id pat)	= "(" ++ (pretty id) ++ "@" ++ (pretty pat) ++ ")"
    pretty (ConPat _ id pats)	= "(" ++ (pretty id) ++ " " ++ (pretty pats) ++ ")"
    pretty (TupPat _ pats)	= "(" ++ (pretty pats) ++ ",)"
    pretty (ListPat _ pats)	= "[" ++ (pretty pats) ++ ",]"
    pretty (LabPat id fpats)	= "(" ++ (pretty id) ++ "{" ++  (pretty fpats) ++ "})"
    pretty (AnnPat _ id ty)	= "(" ++ (pretty id) ++ " :: " ++ (pretty ty) ++ ")"

instance Pretty FieldPat where    
    pretty (FieldPat _ id pat)	= (pretty id) ++ " = " ++ (pretty pat)
    prettySep _ = " , "

instance Pretty RHS where
    pretty (RHS1 exp)		= " = " ++ (pretty exp)
    pretty (RHSG gexps)		= " | " ++ (pretty gexps)

instance Pretty Exp where
    pretty (VarExp id)		= pretty id
    pretty (ConExp id)		= pretty id
    pretty (LitExp l)		= pretty l
    pretty (NegExp _ exp)	= "(-" ++ (pretty exp) ++ ")"
    pretty (AbsExp _ pats exp)	= "\\" ++ (pretty pats) ++ "->" ++ (pretty exp)
    pretty (AppExp _ e1 e2)	= "(" ++ (pretty e1) ++ " " ++ (pretty e2) ++ ")"
    pretty (IfxAppExp _ e1 e2 e3) = "(" ++ (pretty e1) ++ " `" ++ (pretty e2) ++ "` " ++ (pretty e3) ++ ")"
    pretty (PIfxAppExp _ e1 e2 e3) = "(" ++ (pretty e1) ++ " `" ++ (pretty e2) ++ "` " ++ (pretty e3) ++ ")"
    pretty (LetExp _ decs exp) = "( let" ++ (pretty decs) ++ "\n in" ++ (pretty exp) ++ ")"
    pretty (CaseExp _ exp calts) = "( case " ++ (pretty exp) ++ "of \n" ++ (pretty calts) ++ ")"
    pretty (DoExp _ stmts) = "(do {\n" ++ (pretty stmts) ++ "}"
    pretty (IfExp _ e1 _ e2 e3) = "( if " ++ (pretty e1) ++ " then " ++ (pretty e2) ++ " else " ++(pretty e3) ++")"
    pretty (AnnExp _ e annty tschm) = "(" ++ (pretty e) ++ (pretty annty) ++ (pretty tschm) ++ ")"
    pretty (TupExp _ exps)	= "(" ++ (pretty exps) ++ ",)"
    pretty (ListExp _ (Many _ exps))	= "[" ++ (pretty exps) ++ "]"
    pretty (ListCompExp _ exp stmts)    = "[" ++ (pretty exp) ++ "|" ++ (pretty stmts) ++ "]"
    pretty (RecExp id fbs)              = "(" ++ (idStr id) ++ "{" ++ (pretty fbs) ++ "})"
    pretty (UpdExp exp fbs)             = "(" ++ (pretty exp) ++ "{" ++ (pretty fbs) ++ "})"
    pretty (SecLeftExp _ e1 e2)         = "(" ++ (pretty e1) ++ " " ++ (pretty e2) ++ ")"
    pretty (SecRightExp _ e1 e2)        = "(" ++ (pretty e1) ++ " " ++ (pretty e2) ++ ")"
    pretty (EnumFromExp _ e)            = "[" ++ (pretty e) ++ "..]"
    pretty (EnumFromThenExp _ e1 e2)    = "[" ++ (pretty e1) ++ "," ++ (pretty e2) ++ "..]"
    pretty (EnumFromThenToExp _ e1 e2 e3) = "[" ++ (pretty e1) ++ "," ++ (pretty e2) ++ ".." ++ (pretty e3) ++ "]"

instance Pretty FieldBind where
    pretty (FieldBind _ id exp) = (idStr id) ++ "=" ++ (pretty exp)
    prettySep _ = " , "

instance Pretty CaseAlt where
    pretty (CaseAlt _ pat rhs wh) = (pretty pat) ++ "->" ++ (pretty rhs) ++ "\n where \n " ++ (pretty wh)
    prettySep _ = " | "

instance Pretty GdExp where
    pretty (GdExp _ guard exp) = (pretty guard) ++ " = " ++ (pretty exp)
    prettySep _ = " | "

instance Pretty Stmt where
    pretty (GenStmt _ pat exp) = (pretty pat) ++ " <- " ++ (pretty exp)
    pretty (QualStmt _ exp)    = (pretty exp)
    pretty (LetStmt _ decs)    = "let " ++ (pretty decs)
    prettySep _ = " \n "

instance Pretty PatBnd where
    pretty (PatBnd pat rhs wh) = (pretty pat) ++ (pretty rhs) ++ "\n where \n" ++ (pretty wh)

instance Pretty Over where
    pretty (Over0 id) = "overload " ++ (idStr id)
    pretty (OverDef sig defs) = "overload " ++ (pretty sig) ++ (pretty defs)

instance Pretty Class where
    pretty (Class ctxt pred fds wh) = "class (" ++ (pretty ctxt) ++ ") => " ++ (pretty pred) ++  " | " ++ (pretty fds) ++ " where \n " ++ (pretty wh)
    pretty (AFDClass ctxt pred fds afds wh) = "class (" ++ (pretty ctxt) ++ ") => " ++ (pretty pred) ++  " | " ++ (pretty fds) ++ " where \n "
                                              ++ (pretty afds) ++ " \n "  ++ (pretty wh)
    prettySep _ = "\n"

instance Pretty AFDDec where
    pretty (AFDDec _ id1 ids id2) = (pretty id1) ++ " : " ++ (pretty ids) ++ " -> " ++ (pretty id2)
    prettySep _ = "\n"

instance Pretty FunDep where
    pretty (FunDep _ ids ids') = (pretty ids) ++ " -> " ++ (pretty ids')
    prettySep _ = ","

instance Pretty Pred where
    pretty (Pred _ id tys) = (idStr id) ++ (pretty tys)
    prettySep _ = ","

instance Pretty Inst where
    pretty (Inst ctxt pred wh) = "instance (" ++ (pretty ctxt) ++ ")  => " ++ (pretty pred) ++ " where \n" ++ (pretty wh)
    pretty (AFDInst ctxt pred afds wh) = "instance (" ++ (pretty ctxt) ++ ")  => " ++ (pretty pred) ++ " where \n" 
                                         ++ (pretty afds) ++ "\n" ++ (pretty wh)

instance Pretty AFDDef where
    pretty (AFDDef _ id ts t) = (pretty id) ++ " " ++ (pretty ts) ++ " = " ++ (pretty t)
    prettySep _ = "\n"

instance Pretty Fixity where
    pretty (Fix oa op ids) = "infix" ++ (pretty oa) ++ " " ++ (pretty op) ++ " " ++ (pretty ids)

instance Pretty OpAssoc where
    pretty NonAssoc = ""
    pretty LeftAssoc = "l"
    pretty RightAssoc = "r"

instance Pretty OpPrec where
    pretty i = (show i)

instance Pretty PrimVal where
    pretty (Prim id str tschm) = "primitive " ++ (idStr id) ++ " " ++ str ++ " "  ++ (pretty tschm)

instance Pretty Ctxt where
    pretty (Ctxt preds) = pretty preds

instance Pretty Cnst where
    pretty (Cnst prims) = pretty prims

instance Pretty Prim where
    pretty (PredPrim pred) = pretty pred
    pretty (EqPrim _ ty1 ty2) = (pretty ty1) ++ " = " ++ (pretty ty2)
    prettySep _ = ","

instance Pretty Lit where
    pretty (IntegerLit _ _ s) = s
    pretty (FloatLit _ _ _ s) = s
    pretty (CharLit _ c) = ['\'',c,'\'']
    pretty (StrLit _ s)  = '\"' : s ++ "\""
