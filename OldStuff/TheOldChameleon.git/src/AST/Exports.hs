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
-- | Calculates a module's exports. 
-- Also qualifies all exported variable names.
-- NOTE: this is all performed on the internal AST.
--
-- FIXME: 
--  
--  * This can't be so, since type synonyms can also be exported, even
--    though they have been removed from the internal AST.
--
--  * As always, we should be accumulating all errors and reporting them at
--    the end rather than bailing immediately.
-- 
--------------------------------------------------------------------------------

module AST.Exports (
    progExportable, progExports, Imported, Exported(..), impId, impDec,
    qualifyNamesProg, qualifyExported
) where

import List

import Misc
import Misc.ErrorMsg
import AST.Internal
import qualified AST.External as Ext

--------------------------------------------------------------------------------

-- module and all the things it exports
type ModExps = (IdStr, [Exported])

-- | The name of some exported (top-level) entity, includes: values,
-- constructors (data and type), classes etc.
-- In the case of instances, the Id is bogus (but we need it for calculating
-- imports. The code which does thar goes through a list of exported entities
-- and takes those whose id has the expected qualifier.)
data Exported = XVal	Id	    -- ^ exported value dec.
	      | XType	Id Dec	    -- ^ exported type synonym
	      | XClass	Id Dec	    -- ^ exported class
	      | XInst	Id Dec	    -- ^ exported instance
    deriving (Eq, Show)

instance Pretty Exported where
    pretty x = case x of
	XVal  id -> "val " ++ pretty id
	XType  id dec -> "tsyn " ++ pretty id -- ++ ", " ++ pretty dec
	XClass id dec -> "class " ++ pretty id -- ++ ", " ++ pretty dec
	XInst  id dec -> "inst " ++ pretty id -- ++ ", " ++ pretty dec


-- | Imported entities (same structure as exports.)
type Imported = Exported

-- | Qualifies the `Id' of an exported entity by the given `IdStr'
--   representing a module name, without a trailing . (dot).
qualifyExported :: IdStr -> Exported -> Exported
qualifyExported m = appExpId ((m++".")++)

expId :: Exported -> Id
expId (XVal id)	    = id
expId (XType id _)  = id
expId (XClass id _) = id
expId (XInst id _)  = id
-- expId (XTSyn id t) = id

-- | Extracts the Id of an imported entity.
impId :: Imported -> Id
impId = expId

-- | Extracts the Dec out of an exported entity (if there is one.)
impDec :: Imported -> Maybe Dec
impDec (XType _ d)  = Just d
impDec (XClass _ d) = Just d
impDec (XInst _ d)  = Just d
impDec _ = Nothing

appExpId :: (IdStr -> IdStr) -> Exported -> Exported
appExpId f (XVal id)	 = XVal   (id { idStr = f (idStr id) }) 
appExpId f (XType id d)  = XType  (id { idStr = f (idStr id) }) d
appExpId f (XClass id d) = XClass (id { idStr = f (idStr id) }) d
appExpId f (XInst id d)  = XInst  (id { idStr = f (idStr id) }) d
appExpId f e = e
-- expId f (XTSyn id t) = XTSyn   (id { idStr = f (idStr id) }) t


isXVal, isXType, isXClass :: Exported -> Bool
isXVal (XVal _) = True
isXVal _	= False

isXType (XType _ _) = True
isXType _	    = False

isXClass (XClass _ _) = True
isXClass _	      = False

--------------------------------------------------------------------------------

-- | Generates a list of the local, exportable declarations (i.e. all the
-- top-level declarations.)
progExportable :: Prog -> [Exported]
progExportable = exProg

exProg :: Prog -> [Exported]
exProg (Prog [m]) = let ds = moduleDecs m
		    in  concatMap exDec ds
exProg (Prog _) = bug "We don't handle multiple-modules per `Prog' yet (1)"

exDec :: Dec -> [Exported]
exDec d = case d of
    ValDec _ (LetBnd _ id _)	    -> [XVal id]
    ValDec _ (LetBndAnn _ id _ _ _) -> [XVal id]
    
    DataDec _ (DataType id dt) cs -> XType id d : map exCons cs

    ClassDec _ (Class _ (Pred _ id _) _ ms) -> XClass id d : map exMethod ms

    InstDec _ (Inst _ (Pred _ id _) _) -> [XInst id d]

    _ -> []

  where
    exCons (Cons _ _ _ (DataType id _)) = XVal id

    exMethod (Method id _) = XVal id

--------------------------------------------------------------------------------

-- | Returns a list of all the declarations actually exported by this module.
-- That includes stuff imported from other modules.
-- NOTE: probably needs to take an additional argument
progExports :: Prog -> [Exported]
progExports = progExportable

--------------------------------------------------------------------------------
-- Fully qualifies all variables in the program.

-- | Returns the fully-qualified program, a list of modules imported, and a list
-- of all the qualified imports
-- NOTE: The input list contains, for each module, a list of canonical,
--	 fully-qualified exported items.
qualifyNamesProg :: [ModExps] -> Prog -> (Prog, [IdStr], [Imported])
qualifyNamesProg mxs (Prog (m1:m2:_)) = 
    bug "We don't handle multiple-modules per `Prog' yet (2)"
qualifyNamesProg mxs prog@(Prog [Module id _ imports0 _ _]) = {-
  trace ("\nmxs:\n" ++ showLines mxs ++ 
	   "\nmxs':\n" ++ showLines mxs' ++
	   "\nlocal_mxs':\n" ++ showLines local_mxs' ++
	   "\nglobal_mxs':\n" ++ showLines global_mxs' ++
	   "\nallQualIds:\n" ++ showLines allQualIds ++ "\n") -}
	   (qualProg mxs' local_mxs' prog, modsImported, allQualIds)
  where

    -- Modify the export list to match what's actually imported (including
    -- qualification issues.)
    mxs' :: [ModExps]
    mxs' = filter ((not . null) . snd) (qualModExps mxs)
    
    local_mxs', global_mxs' :: [ModExps]
    (local_mxs', global_mxs') = partition (\mx@(m,_) -> m == idStr id) mxs'

    -- These are just the canonically qualified imported ids.
    -- NOTE: This is a bit hacky (we should already have this list, rather than
    --	     regenerating it like this.
    allQualIds :: [Imported]
    allQualIds = [ x | (m,xs) <- global_mxs', x <- xs,
		       m == takeQual (idStr (expId x)) ]


    -- we need to:
    -- a) add an implicit import of the current module
    -- b) remove/consolidate duplicate imports		-- FIXME: TODO!
    imports :: [Import]
    imports = (Import id Unqual ImAll) : imports0
  
    lookupImport :: IdStr -> [Import]
    lookupImport str = [ i | i@(Import id _ _) <- imports, idStr id == str ]
  
    importId :: Import -> IdStr
    importId (Import id _ _) = idStr id
  
    modsImported :: [IdStr]
    modsImported = nub (map importId imports)
    

    -- Go through the list of imports and, for each, extend the ModExps list to
    -- include the appropriately qualified alternative ids.
    -- NOTE: The input list contains lists of canonical, fully qualified items
    --	     for each module.
    qualModExps :: [ModExps] -> [ModExps]
    qualModExps = concatMap perMX
      where
	perMX :: ModExps -> [ModExps]
	perMX mx@(id, xs) = case lookupImport id of
		[]  -> []
		ims -> map (proc mx) ims

	proc :: ModExps -> Import -> ModExps
	proc mx@(id, xs) (Import _ qual imps) = 
	    -- first filter out the exports which we don't import
	    -- FIXME: This doesn't go into classes/instances to filter
	    let xs1 = case imps of
			ImAll	    -> xs
			ImSome spec -> 
			    let imIds = concatMap (map (dropQual . idStr) . 
							imSpecIds) spec
			    in  [ x | x <- xs, dropQual (idStr (expId x)) `elem` imIds ]
			ImHiding spec ->
			    let imIds = concatMap (map (dropQual . idStr) . 
							imSpecIds) spec
			    in  [ x | x <- xs, dropQual (idStr (expId x)) `notElem` imIds ]

		xs2 = map (appExpId dropQual) xs1

	    -- Now generate explicitly qualified versions of these exports.
	    -- NOTE: If the module is explicitly qualified, then we can only 
	    -- refer to its elements via qualified names.  If it's not, then we
	    -- can refer to its contents by either their unqualified, or 
	    -- canonically qualified names.
		xs3 = case qual of
			-- Remove the qualifier on each item, and it to the 
			-- qualified alternatives already present.
			Unqual  -> xs2 ++ xs1
			Qual id -> map (appExpId ((idStr id++".")++)) xs2
		
	    in  {- trace ("\nimps: " ++ show imps ++
		       "\nxs1: " ++ show xs1 ++ 
		       "\nxs2: " ++ show xs2 ++ 
		       "\nxs3: " ++ show xs3) -} (id, xs3)
 
 
----------------------------------------

-- stack of lambda-bound variables (in scope)
type Env = [String]

-- Renames all identifiers to their canonical, fully-qualified names.
-- First list of module exports contains all visible inter-module exports, 
-- second contains only the identifiers bound in this module.
qualProg :: [ModExps] -> [ModExps] -> Prog -> Prog
qualProg mxs local_mxs (Prog ms) = 
    -- trace ("\nmxs:\n" ++ showlist mxs) $ 
	Prog (map qualModule ms)
  where

    qualModule :: Module -> Module
    qualModule (Module id exs ims ds t) = Module id exs ims (map (qualDec []) ds) t

    qualDec :: Env -> Dec -> Dec
    qualDec env (ValDec s lb)   = ValDec s (qualLetBnd env lb)
    qualDec _ (DataDec s dt cs)	= DataDec s (qualDTType dt) (map qualCons cs)
    qualDec _ (ClassDec s c)	= ClassDec s (qualClass c)
    qualDec _ (InstDec s i)	= InstDec s (qualInst i)
    qualDec _ (RuleDec s r)	= RuleDec s (qualRule r)
    qualDec _ (ConsDec s c)     = ConsDec s (qualConstr c)
    qualDec _ d = d

    qualConstr :: Constr -> Constr
    qualConstr (ConstrCls id typ)  = ConstrCls (renameId isXClass local_mxs id) (qualType typ)
    qualConstr (ConstrData id typ) = ConstrData (renameId isXType local_mxs id) (qualType typ)
 
    qualRule :: Rule -> Rule
    qualRule (SimpRule ctxt cnst) = SimpRule (qualCtxt ctxt) (qualCnst cnst)
    qualRule (PropRule ctxt cnst) = PropRule (qualCtxt ctxt) (qualCnst cnst)
 
    qualDT :: (Exported -> Bool) -> DataType -> DataType
    qualDT p (DataType id ts) = DataType (renameId p local_mxs id) 
					 (map qualType ts)

    qualDTVal  = qualDT isXVal
    qualDTType = qualDT isXType
 
    qualInst :: Inst -> Inst
    qualInst (Inst ctxt p w) = Inst (qualCtxt ctxt) (qualPred p) 
				    (map (qualDec []) w)
 
    qualClass :: Class -> Class
    qualClass (Class ctxt p fds ms) = Class (qualCtxt ctxt) (qualPred p) fds
					    (map qualMethod ms)
 
    qualMethod :: Method -> Method
    qualMethod (Method id ts) = Method (renLet id) (qualTSchm ts)
    
    qualCons :: Cons -> Cons
    qualCons (Cons s vs c dt) = Cons s vs (qualCnst c) (qualDTVal dt)

    qualLetBnd :: Env -> LetBnd -> LetBnd
    qualLetBnd env (LetBnd s id e) = LetBnd s (renLet id) (qualExp env e)
    qualLetBnd env (LetBndAnn s id at ts e) = 
				LetBndAnn s (renLet id) at (qualTSchm ts) 
							   (qualExp env e)
    renLet :: Id -> Id
    renLet = renameId isXVal local_mxs
    
    
    qualExp :: Env -> Exp -> Exp
    qualExp env e = case e of
	VarExp id -> VarExp (renVal id)
        ConExp id -> ConExp (renVal id)
        LitExp l  -> e 
        AppExp  s e1 e2 -> AppExp s (qual e1) (qual e2)
        AbsExp  s id e  -> AbsExp s id (qualExp (idStr id:env) e)
        LetExp  s lbs e -> LetExp s (map (qualLetBnd env) lbs) (qual e)
        CaseExp s es ms -> CaseExp s (map qual es) (map (qualMatch env) ms)
      where
	-- renames a let-bound expression identifier
	renVal :: Id -> Id
	renVal id | idStr id `elem` env = id
		  | otherwise = renameId isXVal mxs id

	qual = qualExp env
    
    qualMatch :: Env -> Match -> Match
    qualMatch env (Match ps0 e) = 
		   Match ps (qualExp (concatMap patVars ps0 ++ env) e)
      where
	ps = map qualPat ps0
      
	patVars :: Pat -> [IdStr]
	patVars (VarPat id) = [idStr id]
	patVars (ConPat _ _ ps) = concatMap patVars ps
        patVars (AnnPat _ id _) = [idStr id]
	patVars _ = []

    qualPat :: Pat -> Pat
    qualPat (ConPat s id ps) = ConPat s (renameId isXVal mxs id) 
					(map qualPat ps)
    qualPat (AnnPat s id t) = AnnPat s id (qualType t)
    qualPat p = p

    qualTSchm :: TSchm -> TSchm
    qualTSchm (TSchm ctxt t) = TSchm (qualCtxt ctxt) (qualType t) 

    qualType :: Type -> Type
    qualType t = case t of
	ConType id -> ConType (renameId isXType mxs id)
	AppType s t1 t2 -> AppType s (qualType t1) (qualType t2)
	_ -> t
		
    qualCtxt :: Ctxt -> Ctxt
    qualCtxt (Ctxt ps) = Ctxt (map qualPred ps)

    qualCnst :: Cnst -> Cnst
    qualCnst (Cnst ps) = Cnst (map qualPrim ps)

    qualPrim :: Prim -> Prim
    qualPrim (PredPrim p)     = PredPrim (qualPred p)
    qualPrim (EqPrim s t1 t2) = EqPrim s (qualType t1) (qualType t2)

    qualPred :: Pred -> Pred 
    qualPred p@(Pred s id ts) = Pred s (renameId isXClass mxs id) 
				       (map qualType ts)

----------------------------------------

-- Given a list of modules in scope, and their exports, renames the given id to
-- its canonical qualified name. i.e. if its not qualified, adds a qualifier,
-- if its already qualified, then changes the qualifier to refer directly to
-- the module name.
renameId :: (Exported -> Bool) -> [ModExps] -> Id -> Id
renameId p mxs id = 
    let str = idStr id
	ms  = [ m | (m,exs) <- mxs, x <- exs, p x, str == idStr (expId x) ]
    in  case ms of
	    -- no module exports it (must be lambda-bound, if not then
	    -- we'll catch it during constraint generation)
	    []	-> {- trace ("BUG: didn't find a match for `"++str++"'" ++ 
			  " (This ought to be an error!)") -} id
		    
	    -- there's exactly one source module; that's good!
    	    [m]	-> id { idStr = m ++ "." ++ dropQual str }
		    
	    -- there're multiple candidates; that's bad!
	    _   -> let alts = map (++("."++str)) (sort ms)
		       msg  = errorMsg id 
				["Ambiguous identifier `"++str++"'",
				 "Did you mean "++ commasOr alts ++"?"]
		   in case allEqualAm alts of
                        False -> exit msg
                        True  -> let (x:xs) = alts
                                 in id { idStr = x ++ "." ++ dropQual str}
 

allEqualAm :: [String] -> Bool
allEqualAm (x:y:xs) = case x==y of
                        True  -> allEqualAm (y:xs)
                        False -> False
allEqualAm (y:[])   = True
allEqualAm _        = True
                           

