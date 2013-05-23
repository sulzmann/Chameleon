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
-- Implementor: J. Wazny
-- Maintainer : J. Wazny
--------------------------------------------------------------------------------
-- | This module contains the desugarer, which translates programs in the
-- external language, to semantically equivalent programs in the internal
-- language. This translation preserves all location-specific information in
-- the ASTs.
--
-- The following also occurs during desugaring:
--
--  * type synonyms are expanded
--
--  * we import some implicit primitive modules
--
-- FIXME\TODO: 
--
--  * we should accumulate as many errors as possible before failing
--    (currently we fail at the first error.) This applies to other modules 
--    as well.
--
--  * we should distinguish automatically generated functions to avoid checking
--    them later.
--
--  * make consistent the use of error reporting functions in target program
--    e.g. patternMatchFailed, uninitialisedField, noSuchField
--
--  * undefinedMethod errors contain an ugly reference to the instance 
--    (pretty-print it)
--
--  * See bug related to dsInsts. (to do with default methods)
--
--------------------------------------------------------------------------------

module AST.Desugarer (
    desugarProg
)
where

import List
import Char
import Maybe
import Monad
import Debug.Trace

import AST.SrcInfo
import AST.External as E
import AST.Internal as I
import AST.Operators
import AST.Deriving as D

import Misc
import Misc.Defaults
import Misc.ErrorMsg
import Core.BuiltIn
import Config.Global	(Options(..))

--------------------------------------------------------------------------------

-- constructor arity
type ConArity = (IdStr, Int)

-- we thread through a:
--  - unique number store
--  - type synoym mapping
--  - list of all encountered SrcInfos
--  - table of data constructors with their arrities
--  - table of operator information (prec./assoc.)
--  - a list of all class decs. (to get at any default methods)
--  - all global options
data DSState = St Int SynMap [SrcInfo] [ConArity] OpTable [E.Dec] Options
initDSState = St 1 emptySynMap [] [] emptyOpTable [] (bug "options")

-- desugarer monad
-- contains a fresh name store
newtype DS a = DS (DSState -> (DSState, a))

instance Monad DS where
    -- return :: a -> DS a
    return a = DS (\l -> (l, a))

    -- (>>=) :: DS a -> (a -> DS b) -> DS b
    (DS f) >>= g = DS (\s -> let (s',a) = f $! s
				 DS e = g $! a
                             in  e $! s')

-- runs a desugarer, returning the desuagared result
runDS :: DS a -> a
runDS ds = snd (runDSConf ds)

runDSConf :: DS a -> (DSState, a)
runDSConf (DS f) = f initDSState

-- returns the current label, and updates the internal state
newName :: DS IdStr
newName = DS (\(St n sm is ca ot cs opt) ->
	       (St (n+1) sm is ca ot cs opt, "x$" ++ show n))

newNames :: Int -> DS [IdStr]
newNames n = mapM (const newName) (replicate n newName)

newNum :: DS Int
newNum = DS (\(St n sm is ca ot cs opt) -> (St (n+1) sm is ca ot cs opt, n))

addSyn :: Syn -> DS ()
addSyn s = DS (\(St n sm is ca ot cs opt) -> (St n (s:sm) is ca ot cs opt, ()))

getSynMap :: DS SynMap
getSynMap = DS (\st@(St _ sm is ca ot cs opt) -> (st, sm))

addSrcInfoOf :: HasSrcInfo a => a -> DS ()
addSrcInfoOf x = DS (\st@(St n sm is ca ot cs opt) -> 
			 (St n sm (getSrcInfo x:is) ca ot cs opt, ()))

-- Putting and getting the operator prec./assoc. table
putOpTable :: OpTable -> DS ()
putOpTable ot = DS (\st@(St n sm is ca _ cs opt) -> 
			(St n sm is ca ot cs opt, ()))

getOpTable :: DS OpTable
getOpTable = DS (\st@(St n sm is ca ot cs opt) -> (st, ot))

-- Putting and getting class decs. 
putClassDecs :: [E.Dec] -> DS ()
putClassDecs cs = DS (\st@(St n sm is ca ot _ opt) -> 
			  (St n sm is ca ot cs opt, ()))

getClassDecs :: DS [E.Dec]
getClassDecs = DS (\st@(St n sm is ca ot cs opt) -> (st, cs))


-- Putting and checking options. 
putOptions :: Options -> DS ()
putOptions opt = DS (\st@(St n sm is ca ot cs _) -> 
			 (St n sm is ca ot cs opt, ()))

getOption :: (Options -> a) -> DS a
getOption f = DS (\st@(St n sm is ca ot cs opt) -> (st, f opt))



-- records the arity of the named constructor
setConArity :: IdStr -> Int -> DS ()
setConArity id a = DS (\st@(St n sm is ca ot cs opt) -> 
			   (St n sm is ((id,a):ca) ot cs opt, ()))

-- NOTE: The only time we'll not know the arity is if the constructor is
--	 undefined, and we ought've caught that case already.
lookupConArity :: IdStr -> DS Int
lookupConArity id = DS (\st@(St n sm is ca ot cs opt) -> 
			    (st, case lookup id ca of
					Just a -> a
					Nothing -> 0))


-- basic desugaring combinators (for lifting values into the monad)
(|>) :: Monad m => m (a -> b) -> m a -> m b
f |>  m = f >>= \g -> m >>= \r -> return (g $! r)

(||>) :: Monad m => (a -> b) -> m a -> m b
f ||> m = m >>= \r -> return (f $! r)



-- replaces the unique number in the SrcInfo by a new one
freshen :: SrcInfo -> DS SrcInfo
freshen s = do n <- newNum
	       return (s { srcLoc = n })

instance HasNumSupply DS where
    freshInt = newNum

--------------------------------------------------------------------------------
-- Type synonyms

-- Note: synoyms are transformed into types in the external language, which
-- then need to be `desuagarred' as any other type.

-- Maps a type synonyms (represented by a type constructor), to a
-- concrete type.
-- We record, the synonym id, its arity, and its expansion. The expansion
-- contains distinguished constructors which indicate where the synonym's
-- arguments should be inserted. (These are unary constructors with names of
-- the form $n, where `n' indicates the number of the argument to replace it
-- with.)
data Syn = Syn E.Id Arity E.Type
    deriving Show

-- A set of synonym mappings. 
type SynMap = [Syn]

type Arity = Int

emptySynMap = []

lookupSynMap :: IdStr -> SynMap -> Maybe (Arity, E.Type)
lookupSynMap id sm = listToMaybe [ (a,t) | Syn id' a t <- sm, 
					   id == E.idStr id' ]

--------------------------------------------------------------------------------

-- | Desugars program from external syntax, to the internal while also fixing 
-- operators, and expanding type synonyms. It also returns a list of all the
-- SrcInfos in the external AST.
desugarProg :: Options -> E.Prog -> (I.Prog, SrcInfoTable)
desugarProg opt p = 
    case runDSConf (do putOptions opt
		       dsProg (fixOperators (rmAFDProg p))) of
	(St _ _ is _ _ _ _, ip) -> (ip, mkSrcInfoTable is)

--------------------------------------------------------------------------------

-- convert programs
dsProg :: E.Prog -> DS I.Prog
dsProg (E.Prog ms) = I.Prog ||> dsModules ms 

-- convert modules
-- also add any implicit imports (just Chameleon.Primitive for now)
dsModules :: [E.Module] -> DS [I.Module]
dsModules = mapM dsMod
  where
    dsMod :: E.Module -> DS (I.Module)
    dsMod (E.Module id exs ims ds t) = do
	imp <- getOption importImplicit
	let ims'' = if imp then ims' else ims
	(\a -> I.Module id exs ims'' a (dsModType t)) ||> dsTopDecs ds 
      where
	ims' = newImports ++ ims

	-- NOTE: Implicit modules aren't automatically imported into other
	--       implicit modules.
	newImports | any (==idStr id) implicitImports = []
		   | otherwise = map mkImport implicitImports

	mkImport m = let id = mkId builtInSrcInfo m
	             -- in  Import id (Qual id) (ImSome [ImVar $ anonId "patternMatchFailed"]) 
	             in  Import id (Qual id) ImAll
    dsModType :: E.ModType -> I.ModType
    dsModType E.Cmod = I.Cmod
    dsModType E.Xmod = I.Xmod


-- Convert multiple top-level declarations
-- NOTE: We need to strictly handle the synonym declarations first, since
--       synonyms may appear in any type of subsequent declarations.
-- We also store all the class decs in the DS state, since we may need to add
-- their default methods to instances later.
dsTopDecs :: [E.Dec] -> DS [I.Dec]
dsTopDecs ds0 = do 
    mapM dsTypeDec ds_ts
    checkSynMapCycles
    sm <- getSynMap
    putClassDecs (filter isClassDec ds)
    dss <- mapM dsDec ds
    return (concat dss)
  where
    -- separate the synonym decs from the rest
    (ds_ts, ds_rest) = partition isTypeDec ds0
    isTypeDec (TypeDec {}) = True
    isTypeDec _ = False

    isClassDec (E.ClassDec {}) = True
    isClassDec _ = False

    ds = dropAnnDecs $ mergeDefs ds_rest
  
    mkList :: DS a -> DS [a]
    mkList c = c >>= return . (:[])
  
    dsDec d = addSrcInfoOf d >> dsDec' d
    dsDec' :: E.Dec -> DS [I.Dec]
    dsDec' (E.FixDec _ _)   = return []	    -- already taken care of
    dsDec' (E.RuleDec s r)  = mkList (I.RuleDec s ||> dsRule r)
    dsDec' (E.DataDec s d)  = dsData s d
    dsDec' (E.ExtDec s e)   = bug "we don't allow extern. decs"
    dsDec' (E.TypeDec s ts) = bug "no type synonyms should exist any more"
    dsDec' (E.ClassDec s c) = do 
            let (c',(con:cons))    = expandKindAnn c
                (b,k)              = strUpTypes cons
                (E.ConstrCls id _) = con
            cls <- mkList (I.ClassDec s ||> dsClass c')
            cs  <- mkList (I.ConsDec s ||> dsConstr (E.ConstrCls id k))
            return (cls ++ cs)
    dsDec' (E.InstDec  s i) = mkList (I.InstDec s ||> dsInst s i)
    dsDec' d@(E.PrimDec s p)= mkList (I.PrimDec s ||> dsPrimVal p)
    dsDec' d@(E.PatDec s p) = dsPatDec ds0 d
    dsDec' d@(E.ValDec s f) = do 
	    id <- dsId (defsId f)
	    fs <- dsDefs d
	    mann <- dsAnnDec ds0 (defsId f)
	    case mann of
		Nothing	     -> return [I.ValDec s (LetBnd s id fs)]
		Just (at,ts) -> return [I.ValDec s (LetBndAnn s id at ts fs)]
    dsDec' (E.ConsDec s c)  = mkList (I.ConsDec s ||> dsConstr c)
    dsDec' (E.ExtConsDec s p) = do
            let (p',(con:cons))    = expandKindAnn p
                (b,k)              = strUpTypes cons
                (E.ConstrCls id _) = con
            dsDec' (E.ConsDec s (E.ConstrCls id k))

    dsDec' dec = bug ("deDec, missing case for: " ++ show dec)

strUpTypes :: [E.Constr] -> (Bool, E.Type)
strUpTypes (c:cs) = let (E.ConstrCls id t) = c
                        (b, ts) = strUpTypes cs
                    in case (idStr id) of
                          "var!" -> (b, E.ArrType (idSrcInfo id) (E.VarType id) ts)
                          _      -> (True, E.ArrType (idSrcInfo id) t ts)
strUpTypes []     = (False, E.ConType (anonId "*")) 

dsConstr :: E.Constr -> DS I.Constr
dsConstr (E.ConstrCls id ty)  = I.ConstrCls ||> dsId id |> dsType ty
dsConstr (E.ConstrData id ty) = I.ConstrData ||> dsId id |> dsType ty

dsPrimVal :: E.PrimVal -> DS I.PrimVal
dsPrimVal (E.Prim id str ts) = I.Prim id str ||> dsTSchm ts

-- convert multiple nested declarations 
dsDecs :: [E.Dec] -> DS [I.Dec]
dsDecs ds0 = concatMapM dsDec ds
  where
    ds = dropAnnDecs $ mergeDefs ds0
 
    dsDec d = addSrcInfoOf d >> dsDec' d
    dsDec' :: E.Dec -> DS [I.Dec]
    dsDec' d@(E.PatDec s p) = dsPatDec ds0 d
    dsDec' d@(E.ValDec s f) = do 
	    id <- dsId (defsId f)
	    fs <- dsDefs d
	    mann <- dsAnnDec ds0 (defsId f)
	    return $ case mann of
		Nothing	     -> [I.ValDec s (LetBnd s id fs)]
		Just (at,ts) -> [I.ValDec s (LetBndAnn s id at ts fs)]

    dsDec' dec = bug ("deDec, missing case for: " ++ show dec)

{- TEST -- REMOVE THIS!
dsPatDec :: [E.Dec] -> E.Dec -> DS [I.Dec]
dsPatDec decs pd@(E.PatDec s (E.PatBnd (E.VarPat id) rhs0 w)) = do
    let d  = Def id [] rhs0 w
	vd = E.ValDec s [d]
    dsDecs [vd]
-}


-- Unwraps a pattern declaration into multiple simple variable bindings.
-- We create: - a simple binding for the RHS
--	      - a simple binding for each variable in the pattern
-- We also pass in the complete list of all declarations at this scope, in case
-- there are any relevant signature declarations.
dsPatDec :: [E.Dec] -> E.Dec -> DS [I.Dec]
dsPatDec decs pd@(E.PatDec s (E.PatBnd p0 rhs0 w)) = do
    ([p],rhs) <- removeLitPatsRHS s ([p0],rhs0)
    re  <- dsRHS rhs
    exp <- dsWhere w re
    (p',pe) <- dsPat p
    n <- freshInt
    let vs = fvPat p' []
	ps = map (replace p') vs
	
	rhs_id   = anonId ("patBindRHS" ++ show (getSrcLoc s) ++ "!" ++ show n)
	rhs_bind = let lb = I.LetBnd s rhs_id (pe exp)
		   in  I.ValDec s lb
		
    var_binds <- mapM (mkBind rhs_id) (zip vs ps)
    let binds = rhs_bind : var_binds
    return binds

  where
    
    mkBind :: Id -> (Id, I.Pat) -> DS I.Dec
    mkBind rhs (v,p) = do
	let m   = I.Match [p] (I.VarExp pv)
	    exp = I.CaseExp s [I.VarExp rhs] [m]
	    lb  = I.LetBnd s v exp
	    s   = getSrcInfo v
	mann <- dsAnnDec decs v 
	return $ I.ValDec s $ case mann of
	    Nothing	 -> I.LetBnd s v exp
	    Just (at,ts) -> I.LetBndAnn s v at ts exp
  
    -- A more useful version of dsRHS in this case.
    dsRHS :: E.RHS -> DS I.Exp
    dsRHS (RHS1 r)   = dsExp r
    dsRHS (RHSG ges) = let msg = errorMsg s ["Pattern match failure -- guards\
					     \ exhausted"]
			   err = mkRunTimeError patternMatchFailedStr msg
		       in  dsGdExps err [] [] [] ges
  
    fvPat :: I.Pat -> [Id] -> [Id]
    fvPat (I.VarPat id) ids = id:ids
    fvPat (I.LitPat _)  ids = ids
    fvPat (I.ConPat s _ ps) ids = foldr fvPat ids ps
 
    -- replace the named variable, and all the others by `don't cares'.
    replace :: I.Pat -> Id -> I.Pat
    replace p@(I.VarPat id') id | id' == id = pat_pv
				| otherwise = pat_us
    replace p@(I.LitPat _) _ = p
    replace (I.ConPat s id' ps) id = I.ConPat s id' (map (flip replace id) ps)
    
    pat_pv = I.VarPat pv
    pat_us = I.VarPat us
    pv = anonId "pv!"
    us = anonId "_"
	

-- record type synonym internally 
-- NOTE: we also check that all of the synonym's arguments are variables.
dsTypeDec :: E.Dec -> DS ()
dsTypeDec (E.TypeDec s (TSyn id vs t)) = do
    let arr = length vs
	t' = insPos t
    addSyn (Syn id arr t')
  where
    args = map E.idStr vs

    insPos t = case t of
	E.VarType id	  -> replace id 1 args
        E.ConType id 	  -> t
        E.ArrType s t1 t2 -> E.ArrType s (insPos t1) (insPos t2) 
        E.AppType s t1 t2 -> E.AppType s (insPos t1) (insPos t2)
        E.TupType s ts    -> E.TupType s (map insPos ts)
	E.ListType s t	  -> E.ListType s (insPos t)

    -- go through the list of vars bound by the synonym
    replace id n [] = E.VarType id
    replace eid@(E.Id s id o) n (a:as) 
	| id == a   = mkPos n 
	| otherwise = replace eid (n+1) as

    mkPos n = E.ConType (E.mkId anonSrcInfo ('$' : show n))


-- Convert data type declarations.
-- Also generates all automatically derived instances.
dsData :: SrcInfo -> E.Data -> DS [I.Dec]
dsData s d@(E.Data t vs cs ds) = do 
    dt   <- I.DataType ||> dsId t |> (map I.VarType ||> (mapM dsId vs))
    ics  <- mapM dsCon cs
    fs   <- dsRecCons cs
    decs <- dsDeriving d
    return (I.DataDec s dt ics : fs ++ decs)
dsData s (E.DataKindAnn t ts cs ds) = do
    let vs = extractIds ts
        d  = E.Data t vs cs ds
    cons <- I.ConsDec s ||> dsConstr (E.ConstrData t (makeDataKind s ts))
    dt   <- I.DataType ||> dsId t |> (map I.VarType ||> (mapM dsId vs))
    ics  <- mapM dsCon cs
    fs   <- dsRecCons cs
    decs <- dsDeriving d
    return (I.DataDec s dt ics : fs ++ decs ++ [cons])    			     

extractIds :: [E.Type] -> [Id]
extractIds ((E.VarType id):ts)     = id:(extractIds ts)
extractIds ((E.AnnType _ id _):ts) = id:(extractIds ts)
extractIds (t:ts)                  = extractIds ts
extractIds []                      = []

makeDataKind :: SrcInfo -> [E.Type] -> E.Type
makeDataKind s (t:ts) = let ts' = makeDataKind s ts
                        in case t of
                             (E.VarType _)      -> (E.ArrType s t ts')
                             (E.AnnType s' _ k) -> (E.ArrType s' k ts')
                             _                  -> (E.ArrType s t ts')
makeDataKind s []     = E.ConType (anonId "*")

-- convert data constructor declarations
dsCon :: E.Con -> DS I.Cons
dsCon c = case c of
    E.Con id ts		-> arr id ts >> 
			   I.Cons (getSrcInfo id) [] I.emptyCnst ||>
				    (I.DataType ||> dsId id |> mapM dsType ts)
				    
    E.QCon evs c id ts	-> arr id ts >>
			   I.Cons (getSrcInfo id) ||> (mapM dsId evs) |> 
				    (dsCnst c) |> 
				    (I.DataType ||> dsId id |> mapM dsType ts)
				    
    E.RecCon id fs	-> arr id fs >>
			   I.Cons (getSrcInfo id) [] I.emptyCnst ||>
				    (I.DataType ||> dsId id |> 
				    mapM (dsType . fieldToType) fs)
				    
    E.RecQCon evs c id fs -> arr id fs >>
			     I.Cons (getSrcInfo id) ||> (mapM dsId evs) |> 
				    (dsCnst c) |> (I.DataType ||> dsId id |> 
				    mapM (dsType . fieldToType) fs)
  where
    fieldToType :: E.FieldDef -> E.Type	    
    fieldToType (E.FieldDef _ t) = t

    arr id xs = setConArity (idStr id) (length xs)


-- Generates all the supporting functions for field selection, update etc.
-- FIXME: use more meaningful source info.!
dsRecCons :: [E.Con] -> DS [I.Dec]
dsRecCons rcs0 = return $ concatMap (mkValDecs rcs) fields
  where
    rcs :: [E.Con]
    rcs = [ case c of RecCon id fs -> RecQCon [] true id fs 
		      _ -> c | c <- rcs0 ]
      where
	true = E.Cnst []

    k  = anonId "k"
    x  = anonId "x"
    y  = anonId "y"
    us = anonId "_"

    -- makes a function projecting the given field out of the constructors
    mkValDecs :: [E.Con] -> IdStr -> [I.Dec]
    mkValDecs cs f = 
	-- note: patterns cover all constructor alternatives 
	let ms  = map (mkMatch f) cs
	    (xms, rms) = unzip ms
	    xcse = I.CaseExp anonSrcInfo [I.VarExp y] xms
	    xabs = I.AbsExp anonSrcInfo y xcse
	    xlb  = I.LetBnd anonSrcInfo (anonId f) xabs

	    rcse = I.CaseExp anonSrcInfo [I.VarExp k] rms
	    rabs = I.AbsExp anonSrcInfo y (I.AbsExp anonSrcInfo k rcse)
	    rlb  = I.LetBnd anonSrcInfo (anonId (f ++ "!")) rabs

	in  [I.ValDec anonSrcInfo xlb, I.ValDec anonSrcInfo rlb]

    -- creates matches against the given fieldname for this constructor
    -- The first simply extracts the field, the second replaces it
    mkMatch :: IdStr -> E.Con -> (I.Match, I.Match)
    mkMatch f c = case c of
	RecQCon _ _ id fs -> case fieldPos f c of
	    0 -> let m = noField id (length fs) in (m, m)

	    p -> let len = length fs
	    
		     -- extraction/projection
		     xvs = replicate (p-1) us ++ x : replicate (len - p) us
		     xps = map I.VarPat xvs
		     xpat= I.ConPat (getSrcInfo id) id xps
		     xe  = I.VarExp x
		     xm  = Match [xpat] xe

		     -- replacement
		     (rps,res) = 
			   let tl xs = case xs of { [] -> [] ; (_:ys) -> ys }
			       (as0,bs0) = span (<p) [1..len]
			       as = map (anonId . ('$':) . show) as0
			       bs = map (anonId . ('$':) . show) bs0
			       ps = map I.VarPat (as ++ us : tl bs)
			       es = map I.VarExp (as ++ y : tl bs)
			   in  (ps, es)
		     rpat= I.ConPat (getSrcInfo id) id rps
		     app = I.AppExp anonSrcInfo 
		     re  = foldl app (I.ConExp id) res
		     rm  = Match [rpat] re
		     
		 in  (xm, rm)
	
	Con id ts      -> let m = noField id (length ts) in (m, m)
	QCon _ _ id ts -> let m = noField id (length ts) in (m, m)
      where 
	noField id l = 
	    let p = I.ConPat (getSrcInfo id) id (map I.VarPat (replicate l us))
		e = let con = I.LitExp (I.StrLit anonSrcInfo (idStr id))
			fld = I.LitExp (I.StrLit anonSrcInfo f)
			err = let msg = errorMsg id ["Record contains no field\
						      \ `" ++ f ++ "'"]
			      in  iMkRunTimeError noSuchFieldStr msg
			app = I.AppExp anonSrcInfo
		    in  app (app err con) fld
	    in  Match [p] e
	    
    -- all the fieldnames
    fields :: [IdStr]
    fields = nub [ idStr id | RecQCon _ _ _ as <- rcs, FieldDef id _ <- as ]
  
    -- position (from 1) of the name field in the constructor, 0 is not found
    fieldPos :: IdStr -> Con -> Int
    fieldPos id (RecQCon _ _ _ as) = 
	case [ n | (n,f)<- zip [1..] as, FieldDef x t <- [f], idStr x == id ] of
	    []	-> 0
	    [n] -> n
	    _   -> bug ("repeated fieldname in " ++ show rcs ++ 
			" (should have caught this earlier!")
    
dsClass :: E.Class -> DS I.Class
dsClass (E.Class c p fds w) = I.Class ||> dsCtxt c |> dsPred p 
				      |> mapM dsFunDep fds |> mapM dsMethod w'
  where
    w' = filter isAnn w
    isAnn (E.AnnDec {}) = True
    isAnn _ = False

dsMethod :: E.Dec -> DS I.Method
dsMethod d = case d of
    AnnDec s sig -> dsSig sig
    _ -> bug (errorMsg (getSrcInfo d) ["Class declaration can only \
					 \contain methods"])
  where
    dsSig :: E.Sig -> DS I.Method
    dsSig (Sig id at ts) = I.Method ||> dsId id |> dsTSchm ts

-- We need to add default methods (where the method isn't provided locally.)
dsInst :: SrcInfo -> E.Inst -> DS I.Inst
dsInst info inst@(E.Inst c p w)= I.Inst ||> dsCtxt c |> dsPred p |> dsInstDecs w
  where
    -- If there's any method declared by the class, but not in the instance,
    -- and there's a default method for it, add the default to the instance.
    -- 
    -- FIXME: Currently there's a problem if the class was imported from 
    -- another module. That's because none of the imported decls have been
    -- added to the module yet!
    -- Even if they had been, at this point the imported ids would be fully
    -- qualified, but the local ids have not been! (So there'll probably be no 
    -- class found matching this instance.) 
    -- We need to delay the propagation of default methods until *after* full 
    -- name qualification. i.e. as a separate step.
    dsInstDecs w = do 
	cs <- getClassDecs
	-- find the methods in the matching class
	let cds = let dss = [ ds | (E.ClassDec _ (E.Class _ cp _ ds)) <- cs,
			      predIdStr p == predIdStr cp ]
		  in  if null dss then bug ("dsInst - no matching class for \
					     \instance \n" ++ show inst)
				  else head dss
				  
	    (cas,cvs) = partition isAnnDec cds
	    ca_ids = [ (annDecIdStr ca, ca) | ca <- cas ]
	    cv_ids = [ (valDecIdStr cv, cv) | cv <- cvs ]
	    iv_ids = [ (valDecIdStr iv, iv) | iv <- w ]
	    w' = update cv_ids ca_ids iv_ids
	dsDecs w -- w' SEE ABOVE NOTE
      where
	predIdStr (E.Pred _ id _) = idStr id
	update cvs cas ivs = proc (order cas) ivs
	  where
	    proc [] ivs = map snd ivs
	    proc ((id,ann):cas) ivs = case lookup id ivs of
		Just  _ -> -- instance defines this method
			   proc cas ivs
			   
		Nothing -> -- instance does not define this method, 
			   -- add the default, if there is one (or an error)
		    case lookup id cvs of
			Just cv -> proc cas (("",cv):ivs)

			Nothing -> 
			    let msg = errorMsg info 
					["Instance " ++ show p ++ " does not\
					 \ provide method `" ++ id ++ "'" ]
				exp = mkRunTimeError undefinedMethodStr msg
				def = E.Def (E.mkId info id) [] (E.RHS1 exp) []
				cv  = ("", E.ValDec info [def])
			    in  proc cas (cv:ivs)
	
	order = sortBy (\a b -> compare (fst a) (fst b))
  
    isValDec d = case d of E.ValDec {} -> True ; _ -> False
    isAnnDec d = case d of E.AnnDec {} -> True ; _ -> False

    predIdStr (E.Pred _ id _) = E.idStr id

    annDecIdStr (E.AnnDec _ (E.Sig id _ _)) = E.idStr id
    valDecIdStr (E.ValDec _ (E.Def id _ _ _:_)) = E.idStr id
	

dsFunDep :: E.FunDep -> DS I.FunDep
dsFunDep (E.FunDep s d r) = I.FunDep s ||> mapM dsId d |> mapM dsId r

dsWhere :: E.Where -> I.Exp -> DS I.Exp
dsWhere [] ie = return ie
dsWhere ds ie = do 
    ds' <- dsDecs ds
    let lbs = map funLB ds'
	s = getSrcInfo ds
    return (I.LetExp s lbs ie)
  where
    funLB (I.ValDec _ lb) = lb
    funLB _ = bug "should have detected non-val. binding in `where'"
    

-- looks for an annotation for the named variable
dsAnnDec :: [E.Dec] -> E.Id -> DS (Maybe (I.AnnType, I.TSchm))
dsAnnDec ds id = 
    case matches of
	    [] -> return Nothing
	    (at,ts):_ -> do iat <- dsAnnType at
			    its <- dsTSchm ts
			    return (Just (iat, its))
  where
    matches = concatMap match ds
    match (E.AnnDec _ (E.Sig sid at ts)) | E.idStr id == E.idStr sid = [(at,ts)]
    match _ = []
	
	    
dsAnnType E.Univ  = return I.Univ
dsAnnType E.Exist = return I.Exist

-- convert right-hand side of definitions
-- We pass in the:
-- a) expression to use when no guards are satisfied
-- b) list of variables to scrutinise
-- c) patterns to match
-- d) where clauses
-- e) RHS itself
-- WARNING: It is critical that we check that the number of patterns in all
--	    matches is the same, before type inference! (The number of
--	    don't-care patterns inserted below in the `pattern match failed' 
--	    case must be the same as the number of patterns in all other 
--	    matches. (This is something we haven't enforced here.)
dsRHS :: E.Exp -> [E.Id] -> [E.Pat] -> E.Where -> E.RHS -> DS I.Exp
dsRHS _ _  [] [] (RHS1 r) = dsExp r
dsRHS _ _  [] w  (RHS1 r) = dsExp r >>= dsWhere w
dsRHS e vs ps w  rhs = case rhs of
    RHSG ges -> dsGdExps e vs ps w ges
    RHS1 r   -> do fps <- replicateM (length ps) freshPat
		   (ps',fe) <- dsPats ps
		   r' <- dsExp r
		   r''<- dsWhere w r'
		   let m1 = I.Match ps' (fe r'')
		   m2 <- I.Match (map (mkIVarPat builtInSrcInfo) fps)||> dsExp e
		   ce <- I.CaseExp anonSrcInfo ||> 
				   (map I.VarExp ||> mapM dsId vs) |> 
				   (return [m1,m2])
		   return ce
  where
    freshPat = do n <- newNum
		  return (dontcareStr ++ show n ++ "!")


-- convert guarded expressions 
-- We pass in:
-- a) the expression to use when no guards are satisfied
-- b) the list of variables to scrutinise
-- c) the patterns to match
-- d) any where decs.
dsGdExps :: E.Exp -> [E.Id] -> [E.Pat] -> [E.Dec] -> [E.GdExp] -> DS I.Exp
dsGdExps def vs ps w ges | null ps   = dsExp conds
		         | otherwise = do
    (ps',fe) <- dsPats ps
    cnd <- dsExp conds
    w'  <- dsWhere w cnd
    let m = I.Match ps' w'
    vs' <- mapM dsId vs
    let vs'' = map I.VarExp vs'
	cse  = I.CaseExp anonSrcInfo vs'' [m]
    return (fe cse)
  where			
    conds = foldr mkCond def ges
    mkCond (GdExp s g thn) = \els -> E.IfExp s g s thn els


-- translates a value declaration (really its list of defs), which represent 
-- separate clauses of the same function/value declaration
-- NOTE: Added the special case of a single def with only var pats to aid with
-- debugging. We need a better general desugaring scheme.
dsDefs :: E.Dec -> DS I.Exp
dsDefs (E.ValDec _ []) = bug "FunDec with no Defs!?!"
dsDefs (E.ValDec s ds0) = case ds0 of
  [d@(E.Def _ ps (RHS1 e) w)] | all isVarPat ps -> do
	r  <- dsExp e
	r' <- dsWhere w r
	let e = foldr (I.AbsExp s) r' (map dsVarPat ps)
	return e

  (d:_) -> do
    ds  <- fixLitPats ds0
    vs  <- newNames (length (defPats d))
    cls <- newNames (length ds)
    let ss   = map getSrcInfo ds
	-- ps   = map getSrcInfo (defPats d)
	anon = repeat anonSrcInfo	    
	eids = zipWith E.mkId ss cls
	iids = zipWith I.mkId ss cls
	evs  = zipWith E.mkId anon vs	    -- we don't care about the vars.
	ivs  = zipWith I.mkId anon vs	    -- themselves for error purposes
        ecls = map E.VarExp (tail' eids) ++ 
	       [let msg = errorMsg s ["Pattern match failure"]
		in  mkRunTimeError patternMatchFailedStr msg]
    es <- sequence [dsRHS cl evs ps w rhs | (E.Def _ ps rhs w,cl)<- zip ds ecls]
    let lbs = zipWith3 I.LetBnd ss iids es
	rhs | length ds == 1 = head es
	    | otherwise	     = I.LetExp s lbs (I.VarExp (head iids))
	e = foldr (I.AbsExp s) rhs ivs
    return e
  where
    -- handle literal patterns
    fixLitPats :: [E.Def] -> DS [E.Def]
    fixLitPats = mapM fix
      where
	fix (E.Def id ps rhs w) = do 
	    (ps',rhs') <- removeLitPatsRHS s (ps,rhs)
	    return (E.Def id ps' rhs' w)
  
    defPats (Def _ ps _ _)  = ps

    isVarPat (E.VarPat {}) = True
    isVarPat _ = False
    dsVarPat (E.VarPat id) = id

    tail' [] = []
    tail' xs = tail xs

-- convert literals
dsLit :: E.Lit -> I.Lit
dsLit (E.IntegerLit s int str)   = I.IntegerLit s int str
dsLit (E.FloatLit s float r str) = I.FloatLit s float r str
dsLit (E.StrLit s str)	       = I.StrLit s str
dsLit (E.CharLit s char)       = I.CharLit s char

-- Convert external literals into expressions.
-- This involves applying casting functions `fromInteger' and `fromRational' in
-- the case of Integers and Floats.
dsLitExp :: E.Lit -> I.Exp
dsLitExp l = case l of
    E.IntegerLit s _ _ -> I.AppExp s (fi s) (I.LitExp (dsLit l))
    E.FloatLit s f (n,d) str -> 
	let app = I.AppExp s 
	    ne  = I.LitExp (I.IntegerLit s n (show n))
	    de  = I.LitExp (I.IntegerLit s d (show d))
	in  app (fr s) (app (app (I.VarExp (I.mkId s mkRatioStr)) ne) de)

    _ -> I.LitExp (dsLit l)
  where
    fi s = I.VarExp (I.mkId s fromIntegerStr)
    fr s = I.VarExp (I.mkId s fromRationalStr)


-- convert patterns
-- NOTE: Returns both the pattern, and a function which creates an expression
--	 in which the pattern variables are bound! This is so that I can use
--	 the already-generated, field extraction functions to get at the
--	 contents of labeled patterns. This approach would also make it easier
--	 to add support for views.
-- FIXME: ensure this function is always applied in the right place!
-- FIXME: We don't handle empty labeled patterns properly yet. e.g. (T {})
dsPat :: E.Pat -> DS (I.Pat, I.Exp -> I.Exp)
dsPat p = addSrcInfoOf p >> dsPat' p
dsPat' p = case p of
    E.VarPat id  -> tup (I.VarPat ||> (dsId id))
    E.LitPat lit -> tup (I.LitPat ||> return (dsLit lit))

    E.ConPat s id pats -> do (ps,fe) <- dsPats pats
			     p <- I.ConPat s ||> (dsId id) |> (return ps)
			     return (p, fe)
    E.TupPat s pats    -> do (ps,fe) <- dsPats pats
			     let n = length pats
			     p <- I.ConPat s (I.mkId s (tupleStr n)) ||>
						       (return ps)
			     return (p, fe)
    E.ListPat s pats   -> do (ps,fe) <- dsPats pats
			     let n = length pats
			     p <- I.ConPat s (I.mkId s (nListStr n)) ||>
						       (return ps)
			     return (p, fe)
    E.AnnPat s id ty   -> tup (I.AnnPat s ||> (dsId id) |> (dsType ty))

    -- E.AsPat s id p     -> do 
    
    -- FIXME: This is a supremely inefficient translation.
    --	      We should be able to do this with one case expression.
    E.LabPat id fs     -> do es <- mapM mkCase fs
			     ar <- lookupConArity (idStr id)
			     let fe e = foldr ($) e es
				 ps = map I.VarPat (replicate ar us)
				 cp = I.ConPat (getSrcInfo id) id ps
				 cse e = I.CaseExp anonSrcInfo [I.VarExp x]
						   [Match [cp] (fe e)]
			     return (I.VarPat x, cse)
      where
	x  = anonId "x!"
	us = anonId "_"

	mkCase :: E.FieldPat -> DS (I.Exp -> I.Exp)
	mkCase (FieldPat s id p) = do
	    -- apply the projection function, case over the result
	    (p',fe) <- dsPat p
	    let e = I.AppExp s (I.VarExp id) (I.VarExp x)
		m = Match [p'] 
		f = \x -> I.CaseExp s [e] [m (fe x)]	
	    return f

  where
    tup :: DS a -> DS (a, b -> b)
    tup ds = ds >>= \a -> return (a, id)


dsPats :: [E.Pat] -> DS ([I.Pat], I.Exp -> I.Exp)
dsPats ps = do
    pes <- mapM dsPat ps
    let (ps',es) = unzip pes
	fes e = foldr ($) e es
    return (ps', fes)

-- convert expressions
dsExp :: E.Exp -> DS I.Exp
dsExp x = addSrcInfoOf x >> dsExp' x
dsExp' (E.VarExp id)  = I.VarExp ||> (dsId id)
dsExp' (E.ConExp id)  = I.ConExp ||> (dsId id)
dsExp' (E.LitExp lit) = return (dsLitExp lit)
dsExp' (E.NegExp s e) = I.AppExp s (mkIVarExp s negateStr) ||> (dsExp e)
dsExp' (E.AbsExp s ps e)  = dsAbs s ps e
dsExp' (E.AppExp s e1 e2) = I.AppExp s ||> dsExp e1 |> dsExp e2
dsExp' (E.IfxAppExp s e1 e2 e3) = do e2' <- dsExp e2
				     foldl (I.AppExp s) e2' ||> 
					   (mapM dsExp [e1, e3])
dsExp' (E.LetExp s ds e)  = do le <- dsWhere ds =<< dsExp e
			       return (newSrcInfo s le)

dsExp' x@(E.CaseExp s e as) = dsCase x  

dsExp' e@(E.DoExp _ _)	 = dsExp =<< unfoldDoExp e

dsExp' (E.IfExp s1 e1 s2 e2 e3) = do addSrcInfoOf s2
				     m1 <- Match [truePatCon s1]  ||> dsExp e2
				     m2 <- Match [falsePatCon s1] ||> dsExp e3
				     ie1 <- dsExp e1
				     return (I.CaseExp s2 [ie1] [m1,m2])
				    
dsExp' (E.AnnExp s e at ts) = do nm <- newName
				 let id  = I.mkId s nm
				     con | at == E.Univ = letBndUAnn
					 | otherwise    = letBndEAnn
				 lb <- con s id ||> dsTSchm ts |> dsExp e
				 return (I.LetExp s [lb] (I.VarExp id))

dsExp' e@(E.ListCompExp _ _ _) = dsExp =<< unfoldListCompExp e

dsExp' (E.TupExp s es) = let con = tupleExpCon s (length es)
			 in  foldl (I.AppExp s) con ||> mapM dsExp es

dsExp' (E.ListExp s1 (Many s2 es)) = do let nil  = I.ConExp (I.mkId s2 listStr)
					    cons = I.ConExp (I.mkId s2 consStr)
					    app  = I.AppExp s1 
					des <- mapM dsExp es
					return (foldr (app . app cons) nil des)

dsExp' (E.RecExp id fs) = -- arrgh, we need to know the constructor arity! 
			  do ar <- lookupConArity (idStr id)
			     let undef= let msg = errorMsg id ["Uninitialised\
						    \ record field accessed"]
					in  mkRunTimeError 
						uninitialisedFieldStr msg
				 app  = E.AppExp anonSrcInfo
				 init = foldl app (E.ConExp id) 
						  (replicate ar undef)
				 upd  = E.UpdExp init fs
			     dsExp' upd
			  
dsExp' (E.UpdExp e  fs) = do e' <- dsExp e
			     ts <- dsFieldBinds fs
			     let (ss,ids,xs) = unzip3 ts
				 xfs = [ v | (id, x) <- zip ids xs, 
					     let id' = id {idStr=idStr id++"!"}
						 f = I.VarExp id'
						 v = I.AppExp anonSrcInfo f x ]
				 app = I.AppExp 
				 exp = foldr (uncurry app) e' (zip ss xfs)
			     return exp

dsExp' (E.SecLeftExp s e1 e2)  = I.AppExp s ||> dsExp e2 |> dsExp e1
dsExp' (E.SecRightExp s e1 e2) = I.AppExp s ||> dsExp e1 |> dsExp e2
dsExp' (E.EnumFromExp s e)     = I.AppExp s (mkIVarExp s enumFromStr)||> dsExp e
dsExp' (E.EnumFromToExp s e1 e2) = foldl (I.AppExp s)
					 (mkIVarExp s enumFromToStr) ||>
					 (mapM dsExp [e1, e2])
dsExp' (E.EnumFromThenExp s e1 e2) = foldl (I.AppExp s)
					  (mkIVarExp s enumFromThenStr) ||> 
					  (mapM dsExp [e1, e2])
dsExp' (E.EnumFromThenToExp s e1 e2 e3) = foldl (I.AppExp s)
					    (mkIVarExp s enumFromThenToStr) ||>
					    (mapM dsExp [e1, e2, e3])
dsExp' e = bug ("expression " ++ show e ++ " not desugared")

dsFieldBinds :: [E.FieldBind] -> DS [(SrcInfo, Id, I.Exp)]
dsFieldBinds = mapM dsFB 
  where
    dsFB (E.FieldBind s id e) = dsExp e >>= \e' -> return (s, id, e')


-- Converts a case-expression into an equivalent internal expression.
dsCase :: E.Exp -> DS I.Exp
dsCase (E.CaseExp s exp cas0) = do
    cas <- fixLitPats cas0
    dsCaseAlts (reverse cas)
  where
    -- handle literal patterns
    fixLitPats :: [CaseAlt] -> DS [CaseAlt]
    fixLitPats = mapM fix
      where
	fix (E.CaseAlt s p rhs w) = do 
	    ([p'],rhs') <- removeLitPatsRHS s ([p],rhs)
	    return (E.CaseAlt s p' rhs' w)
  
    -- Convert a list of case alts (which all appear in the same case).
    -- Guards make it complicated.
    dsCaseAlts :: [E.CaseAlt] -> DS I.Exp
    dsCaseAlts cas = do
	[nm] <- newNames 1		    -- the lambda-bound arg.
	cls  <- newNames (length cas)	    -- the per-alternative decs.
	let lv = E.mkId s nm
	    ss = map getSrcInfo cas
	    eids = zipWith E.mkId ss cls
	    iids = zipWith I.mkId ss cls
	    ecls = map E.VarExp (tail' eids) ++ 
		    [let msg = errorMsg s ["Pattern match failure"]
		     in  mkRunTimeError patternMatchFailedStr msg]
	es <- sequence [dsRHS cl [lv] [p] w rhs | 
			(E.CaseAlt _ p rhs w, cl) <- zip cas ecls ]
	exp' <- dsExp exp
	let lbs = zipWith3 I.LetBnd ss iids es
	    rhs | length cas == 1 = I.AbsExp s lv (head es)
		| otherwise       = I.AbsExp s lv (I.LetExp s lbs 
					             (I.VarExp (head iids)))
	    e = I.AppExp s rhs exp'
	return e

      where
	altPats (E.CaseAlt _ p _ _)  = p

	tail' [] = []
	tail' xs = tail xs


-- convert rules
dsRule :: E.Rule -> DS I.Rule
dsRule (E.PropRule ctxt cnst) = I.PropRule ||> (dsCtxt ctxt) |> (dsCnst cnst)
dsRule (E.SimpRule ctxt cnst) = I.SimpRule ||> (dsCtxt ctxt) |> (dsCnst cnst)

-- convert constraints
dsCtxt :: E.Ctxt -> DS I.Ctxt
dsCtxt (E.Ctxt preds) = I.Ctxt ||> (mapM dsPred preds)

dsCnst :: E.Cnst -> DS I.Cnst
dsCnst (E.Cnst prims) = I.Cnst ||> (mapM dsPrim prims)

dsPred (E.Pred s id typs) = I.Pred s ||> (dsId id) |> mapM dsType typs

dsPrim x = addSrcInfoOf x >> dsPrim' x
dsPrim' (E.PredPrim pred)      = I.PredPrim ||> (dsPred pred)
dsPrim' (E.EqPrim s typ1 typ2) = I.EqPrim s ||> (dsType typ1) |> (dsType typ2)

-- convert types
-- NOTE: we expand all type synonyms at this point
dsType :: E.Type -> DS I.Type
dsType (E.VarType id)  	       = I.VarType ||> (dsId id)
dsType (E.ArrType s typ1 typ2) = foldl (I.AppType s) (arrowTypeCon s) ||>
				       (mapM dsType [typ1,typ2])
dsType (E.TupType s typs)      = let n = length typs 
				 in  if n == 1 
				     then dsType (head typs) 
				     else foldl (I.AppType s) 
					    (tupleTypeCon s n) ||>
					    (mapM dsType typs)
dsType (E.ListType s typ)      = I.AppType s (listTypeCon s) ||> (dsType typ)
dsType t@(E.ConType id)        = do
    mt' <- expandSyn t 
    case mt' of 
	Nothing -> I.ConType ||> (dsId id)
	-- FIXME: see the note below about re-testing t'
	Just t' -> dsType t'
dsType t@(E.AppType s typ1 typ2) = do 
    mt' <- expandSyn t
    case mt' of 
	Nothing -> do 
	    mtyp2' <- expandSyn typ2
	    case mtyp2' of
		Nothing	   -> I.AppType s ||> (dsType typ1) |> (dsType typ2)
		Just typ2' -> I.AppType s ||> (dsType typ1) |> (dsType typ2')
	-- FIXME: t' is going to be re-tested to see if it's a synonym, but it
	--	  can never be one. Skip this test somehow.
	Just t' -> dsType t'

dsType t@(E.AnnType s id typ) = dsType (E.VarType id)

dsType (E.StarType s typ)     = I.AppType s (starTypeCon s) ||> (dsType typ)
dsType (E.UnionType s [typ1,typ2]) = do 
                                     [typ1',typ2'] <- mapM dsType [typ1,typ2]
                                     return (I.AppType s (I.AppType s (unionTypeCon s) typ1') typ2')
dsType (E.UnionType s (typ:typs)) | (length typs) > 1 = do 
                                                       typ2 <- dsType (E.UnionType s typs)
                                                       typ1 <- dsType typ
                                                       return (I.AppType s (I.AppType s (unionTypeCon s) typ1) typ2)
dsType (E.UnionType s _) = bug "dsType failed: union type has less than two arguments!"
dsType (E.EmpType s) = return (empTypeCon s)
dsType (E.OptionType s t) = do
                            t' <- dsType t
                            return (I.AppType s (I.AppType s (unionTypeCon s) (empTypeCon s)) t')
dsType E.PhiType = return (phiTypeCon anonSrcInfo)

-- convert type schemes
dsTSchm :: E.TSchm -> DS I.TSchm
dsTSchm (E.TSchm c t) = I.TSchm ||> dsCtxt c |> dsType t


-- convert ids
dsId :: E.Id -> DS I.Id
dsId id = addSrcInfoOf id >> return id

--------------------------------------------------------------------------------

-- The following are miscellaneous desugaring functions which have been 
-- factored out, since they're used by multiple transformers.

-- desugar an abstraction defined by the given patterns and expression
dsAbs :: SrcInfo -> [E.Pat] -> E.Exp -> DS I.Exp
dsAbs s pats0 eexp0 = do
    (pats,eexp) <- removeLitPatsExp s (pats0,eexp0)
    iexp  <- dsExp eexp
    names <- newNames (length pats)
    let ss  = map getSrcInfo pats
        ids = zipWith I.mkId ss names
        iexps = map I.VarExp ids
    (ipats,fe) <- dsPats pats
    let match = I.Match ipats iexp
        cas = I.CaseExp s iexps [match]
        abs = foldr (I.AbsExp s) cas ids
    return (fe abs)

mkIVarExp :: SrcInfo -> String -> I.Exp
mkIVarExp s = I.VarExp . I.mkId s

mkEVarExp :: SrcInfo -> String -> E.Exp
mkEVarExp s = E.VarExp . E.mkId s

mkIVarPat :: SrcInfo -> String -> I.Pat
mkIVarPat s = I.VarPat . I.mkId s

-- breaks a list comprehension into an expression without `Stmt's
unfoldListCompExp :: E.Exp -> DS E.Exp
unfoldListCompExp (ListCompExp s e ss) = unfold ss
  where
    unfold :: [E.Stmt] -> DS E.Exp
    unfold [] = return $ ListExp s (Many s [e])
    unfold (QualStmt s e:ss)  = do thn <- unfold ss
				   let els = empty s
				   return $ E.IfExp s e s thn els

    unfold (GenStmt s p e:ss) = do nm <- newName
				   ok <- unfold ss
				   let id = E.mkId s nm
				       d1 = E.ValDec s [E.Def id [p] 
							 (E.RHS1 ok) []]
				       d2 = E.ValDec s [E.Def id [p]
							 (E.RHS1 (empty s)) []]
				       cm = foldl (E.AppExp s)
					      (E.VarExp (E.mkId s concatMapStr))
					      [E.VarExp id, e]
				   return $ E.LetExp s [d1,d2] cm
				   
    unfold (LetStmt s ds:ss)  = do rest <- unfold ss
				   return $ E.LetExp s ds rest

    empty s = E.ListExp s (Many s [])

-- breaks a do expression into an expression without `Stmt's
unfoldDoExp :: E.Exp -> DS E.Exp
unfoldDoExp (DoExp s ss) = unfold ss
  where
    seq  s e1 e2 = E.IfxAppExp s e1 (mkEVarExp s mSeqStr)  e2
    bind s e1 e2 = E.IfxAppExp s e1 (mkEVarExp s mBindStr) e2

    unfold :: [E.Stmt] -> DS E.Exp
    unfold [QualStmt s e]     = return e
    unfold (QualStmt s e:ss)  = seq s e ||> unfold ss
    unfold (GenStmt s p e:ss) = (bind s e . (E.AbsExp s [p])) ||> unfold ss
    unfold (LetStmt s ds:ss)  = E.LetExp s ds ||> unfold ss

----------------------------------------

-- Replaces literal patterns by guarded alternatives, using (==).
-- Use this for eliminatig literal pats. in: cases, val. defs, pat. defs
removeLitPatsRHS :: SrcInfo -> ([E.Pat], E.RHS) -> DS ([E.Pat], E.RHS)
removeLitPatsRHS s psr@(ps,rhs) = do
    (m, ps') <- replaceLitPats ps
    case m of
	[] -> -- no literal patterns were replaced, nothing to do
	      return psr

	idls -> let lg = map (uncurry mkEq) idls
		    gd | singleton idls = head lg
		       | otherwise      = foldl1 and lg
		    rhs' = extendGuards gd rhs
		in  return (ps', rhs')
  where

    mkEq id l = E.AppExp s (E.AppExp s (E.VarExp (E.mkId s bEqualsStr)) 
				       (E.VarExp id)) (E.LitExp l)
 
    and = \e1 e2 -> E.AppExp s (E.AppExp s (E.VarExp (E.mkId s bAndStr)) 
					    e1) e2
 
    extendGuards g (RHS1 e)   = RHSG [GdExp s g e]
    extendGuards g (RHSG ges) = RHSG (map extend ges)
      where
	extend (GdExp i g0 e) = GdExp i (and g g0) e

-- Replaces literal patterns by conditional expressions.
-- Use this for lambda abstractions.
removeLitPatsExp :: SrcInfo -> ([E.Pat], E.Exp) -> DS ([E.Pat], E.Exp)
removeLitPatsExp s pse@(ps, e) = do
    (m, ps') <- replaceLitPats ps
    case m of
	[] -> -- no literal patterns were replaced, nothing to do
	      return pse

	[(id,l)] -> let e' = mkCond (mkEq id l)
		    in  return (ps', e')
	
	idls -> let and = \e1 e2 -> (E.AppExp s (E.AppExp s 
				       (E.VarExp (E.mkId s bAndStr)) e1) e2)
		    e' = mkCond (foldl1 and (map (uncurry mkEq) idls))
		in  return (ps', e')
    where

      mkEq id l = E.AppExp s (E.AppExp s (E.VarExp (E.mkId s bEqualsStr)) 
					 (E.VarExp id)) (E.LitExp l)

      mkCond c = E.IfExp s c s e pmf
      
      pmf = let msg = errorMsg s ["Pattern match failure -- couldn't\
				  \ match literal pattern"]
	    in  mkRunTimeError patternMatchFailedStr msg


-- Replaces each literal in the given patterns by a fresh variable. Returns a
-- list associating each new variable to the literal it replaced.
replaceLitPats :: [E.Pat] -> DS ([(E.Id, E.Lit)], [E.Pat])
replaceLitPats ps = thread [] ps
  where
    replace :: [(E.Id, E.Lit)] -> E.Pat -> DS ([(E.Id, E.Lit)], E.Pat)
    replace m p = case p of

	E.VarPat id -> return (m, p)
	
	E.LitPat l -> do nm <- newName 
			 let id = E.mkId (getSrcInfo l) nm
			     p  = E.VarPat id
			 return ((id,l):m, p)
		       
	E.AsPat s id p1  -> do (m',p2) <- replace m p1
			       return (m', E.AsPat s id p2)
			     
	E.ConPat s id ps -> threadApp m ps (E.ConPat s id)
	E.TupPat s ps    -> threadApp m ps (E.TupPat s)
	E.ListPat s ps   -> threadApp m ps (E.ListPat s)

	E.LabPat id fs   -> do let pfs = map splitFieldPat fs
				   (ps,es) = unzip pfs
			       (m',ps') <- thread m ps
			       let fs' = zipWith ($) es ps'
			       return (m', E.LabPat id fs')
        E.AnnPat s id t -> return (m, p)                                                                     
        _ -> do bug ((show m)++(show p))
    splitFieldPat :: E.FieldPat -> (E.Pat, E.Pat -> E.FieldPat)
    splitFieldPat (E.FieldPat s id p) = (p, E.FieldPat s id)

    threadApp :: [(E.Id, E.Lit)] -> [E.Pat] -> ([E.Pat] -> E.Pat)
	      -> DS ([(E.Id, E.Lit)], E.Pat)
    threadApp m ps f = thread m ps >>= \(m',ps') -> return (m', f ps')

    thread :: [(E.Id, E.Lit)] -> [E.Pat] -> DS ([(E.Id, E.Lit)], [E.Pat])
    thread m ps = proc m [] ps >>= \(m',ps') -> return (m', reverse ps')
      where
	proc m a [] = return (m, a)
	proc m a (p:ps) = do (m',p') <- replace m p
			     proc m' (p':a) ps
			 

--------------------------------------------------------------------------------
-- Automatically derived instances.

-- Generates all the derived instances for the given data dec.
dsDeriving :: E.Data -> DS [I.Dec]
dsDeriving d = do ot <- getOpTable
		  return (D.derive ot d)

--------------------------------------------------------------------------------
-- Expanding type synonyms
-- NOTE: We apply type synonyms to external types, resulting in new,
--	 tranformed external types 
--	 (desugaring to internal types occurs as usual.)

-- Attempts to expand given type, returns the new type if expansion occurred,
-- else Nothing.
expandSyn :: E.Type -> DS (Maybe E.Type)
expandSyn t =
    case deconstruct t of
	Nothing -> return Nothing
	Just (E.ConType id, ts) -> do
	    sm <- getSynMap
	    let num_args = length ts
	    case lookupSynMap (E.idStr id) sm of
		Nothing -> -- not a synonym
			   return Nothing
		Just (a,t') 
		    | a /= num_args ->	-- arguments don't match arity
			let txt = "Synonym applied to too " ++ 
				  if a < num_args then "few" else "many" ++ 
				  " types"
			    msg = errorMsg t [txt]
			in  bug msg

		    | otherwise -> return (Just (replace ts t'))
  where
    -- replaces synonym type place holders with actual types at use site
    replace :: [E.Type] -> E.Type -> E.Type
    replace ts t = case t of
        E.ArrType s t1 t2 -> E.ArrType s (rep t1) (rep t2) 
        E.AppType s t1 t2 -> E.AppType s (rep t1) (rep t2)
        E.TupType s ts    -> E.TupType s (map rep ts)
        E.ListType s t	  -> E.ListType s (rep t)
        E.ConType (E.Id s ('$':n) o) 
	    | all isDigit n -> let pos = read n
			       in  ts !! (pos-1)
	_ -> t
      where
	rep = replace ts


-- If the given type is of the form: ((C @ t_1) @ t_2) @ ... t_n
-- then return C and t_1,...,t_n, else Nothing.
deconstruct :: E.Type -> Maybe (E.Type, [E.Type])
deconstruct t = case tts t of
      Nothing -> Nothing
      Just f  -> Just (f [])
  where 
    tts :: E.Type -> Maybe ([E.Type] -> (E.Type, [E.Type]))
    tts (E.AppType _ tc@(E.ConType _) t1) = return $ \ts -> (tc, t1:ts)
    tts (E.AppType _ t1 t2) = do lc <- tts t1
				 let (tc, ts) = lc [t2]
				 return $ \ts' -> (tc, ts ++ ts')
    tts tc@(E.ConType _) = return $ const (tc, [])
    tts _ = Nothing

----------------------------------------
-- Checking the synonym map for cycles.

checkSynMapCycles :: DS ()
checkSynMapCycles = do
    sm <- getSynMap
    let ids  = [ id | Syn id _ _ <- sm ]
        deps = map (procSyn sm [] . E.idStr) ids
        cycs = [ id | (id,ds) <- zip ids deps, E.idStr id `elem` ds ]
    unless (null cycs) (do
	let msg s = errorMsgLine (getSrcInfo s) 
			     ["Cyclical type synonym `" ++ E.idStr s ++ "'"]
	    str   = unlines (map msg cycs)
	bug str) 
  where
    -- FIXME: Use a Set or some other more-efficient structure for the history
    procSyn :: SynMap -> [IdStr] -> IdStr -> [IdStr]
    procSyn sm ss id = 
	case lookupSynMap id sm of
	    Nothing    -> ss
	    Just (_,t) -> let ids  = map E.idStr (typeCons [] t)
			      ids' = filter (`notElem`ss) ids
			  in  if null ids'
			      then ss	    -- fixed point
			      else thread (ids'++ss) ids'
      where
	thread ss [] = ss
	thread ss (id:ids) = let ss' = procSyn sm ss id
			     in  thread ss' ids

    -- find all the constructor ids in the given type
    typeCons :: [E.Id] -> E.Type -> [E.Id]
    typeCons cs t = case t of 
	E.VarType id	  -> cs
        E.ConType id 	  -> id : cs
        E.ArrType s t1 t2 -> typeCons (typeCons cs t1) t2
        E.AppType s t1 t2 -> typeCons (typeCons cs t1) t2
        E.TupType s ts    -> thread cs ts
	E.ListType s t	  -> typeCons cs t
      where
	thread cs [] = cs
	thread cs (t:ts) = thread (typeCons cs t) ts

--------------------------------------------------------------------------------
-- Run-time errors

-- Creates an expression which causes a run-time error by applying the named
-- function to some error message string.
mkRunTimeError :: String -> String -> E.Exp
mkRunTimeError f str = let s = builtInSrcInfo
			   fun = E.VarExp (E.mkId s f)
			   msg = E.LitExp (E.StrLit s str)
		       in  E.AppExp s fun msg


iMkRunTimeError :: String -> String -> I.Exp
iMkRunTimeError f str = let s = builtInSrcInfo
			    fun = I.VarExp (I.mkId s f)
			    msg = I.LitExp (I.StrLit s str)
		        in  I.AppExp s fun msg

--------------------------------------------------------------------------------------------

-- Procedures to process declarations with kind annotations

class MayContainKindAnn a where
   expandKindAnn :: a -> (a,[E.Constr])

instance MayContainKindAnn a => MayContainKindAnn [a] where
   expandKindAnn (a:as) = let (a',d1)  = expandKindAnn a
                              (as',d2) = expandKindAnn as
                          in (a':as',d1 ++ d2)
   expandKindAnn []     = ([],[])

instance MayContainKindAnn E.Class where
   expandKindAnn (E.Class c p f w) = let (p',decs) = expandKindAnn p
                                     in (E.Class c p' f w, decs)

instance MayContainKindAnn E.Pred where
   expandKindAnn (E.Pred s id ts) = let (ts',decs) = expandKindAnn ts
                                    in (E.Pred s id ts', (E.ConstrCls id (E.VarType id)):decs)

instance MayContainKindAnn E.Type where
   expandKindAnn (E.AnnType s id typ) = (E.VarType id, [E.ConstrCls id typ])
   expandKindAnn t                    = (t, [E.ConstrCls (anonId "var!") t])

----------------------------------------------------------------------------------------------

-- Procedures to translate declarations with Associated Functional Dependencies

rmAFDProg :: E.Prog -> E.Prog
rmAFDProg (E.Prog ms) = E.Prog (rmAFDMods ms)

rmAFDMods :: [E.Module] -> [E.Module]
rmAFDMods (m:ms) = 
   let m' = rmAFDMod m
   in m':(rmAFDMods ms)
   where
      rmAFDMod :: E.Module -> E.Module
      rmAFDMod (E.Module id exs ims decs t) = 
          let decs' = rmAFDDecs decs
          in E.Module id exs ims decs' t
      rmAFDMod xm = xm
rmAFDMods [] = []

rmAFDDecs :: [E.Dec] -> [E.Dec]
rmAFDDecs (d:ds) = 
   let d'  = rmAFDDec d
       ds' = rmAFDDecs ds
   in (d' ++ ds')
rmAFDDecs [] = []

rmAFDDec :: E.Dec -> [E.Dec]
rmAFDDec (E.RuleDec src r) = 
   let r' = rmAFDRule r
   in [E.RuleDec src r']
rmAFDDec (E.DataDec src d) =
   let d' = rmAFDData d
   in [E.DataDec src d']
rmAFDDec (E.AnnDec src sig) =
   let sig' = rmAFDSig sig
   in [E.AnnDec src sig']
rmAFDDec (E.ClassDec src cls) =
   let (cls',decs) = rmAFDClass cls
   in ((E.ClassDec src cls'):decs)
rmAFDDec (E.InstDec src inst) =
   let (inst',decs) = rmAFDInst inst
   in (E.InstDec src inst'):decs 
rmAFDDec dec = [dec]

rmAFDRule :: E.Rule -> E.Rule
rmAFDRule r = r 

rmAFDData :: E.Data -> E.Data
rmAFDData d = d

rmAFDSig :: E.Sig -> E.Sig
rmAFDSig (E.Sig id ann tschm) = E.Sig id ann (rmAFDTSchm tschm)

rmAFDTSchm :: E.TSchm -> E.TSchm
rmAFDTSchm (E.TSchm ctxt ty) = 
   let (n,ctxt')    = rmAFDCtxt 0 ctxt
       (n',ps,ty')  = rmAFDType n ty
   in (E.TSchm (mergeCtxt ctxt' (E.Ctxt ps)) ty')

rmAFDType :: Int -> E.Type -> (Int,[E.Pred],E.Type)
rmAFDType n (E.ArrType src t1 t2) = 
   let (n',p1,t1')  = rmAFDType n t1
       (n'',p2,t2') = rmAFDType n' t2
   in (n'',p1++p2,E.ArrType src t1' t2') 
rmAFDType n (E.AppType src t1 t2) = 
   let (n',p1,t1')  = rmAFDType n t1
       (n'',p2,t2') = rmAFDType n' t2
   in (n'',p1++p2,E.AppType src t1' t2')
rmAFDType n (E.TupType src ts) =
   let (n',p,ts') = rmAFDTypes n ts
   in (n',p,E.TupType src ts')
rmAFDType n (E.ListType src t) =
   let (n',p,t') = rmAFDType n t
   in (n',p,E.ListType src t')
rmAFDType n (E.UnionType src ts) =
   let (n',p,ts') = rmAFDTypes n ts
   in (n',p,E.UnionType src ts')
rmAFDType n (E.StarType src t) =
   let (n',p,t') = rmAFDType n t
   in (n',p,E.StarType src t')
rmAFDType n (E.OptionType src t) =
   let (n',p,t') = rmAFDType n t
   in (n',p,E.OptionType src t')
rmAFDType n (E.AnnType src id t) =
   let (n',p,t') = rmAFDType n t
   in (n',p,E.AnnType src id t')
rmAFDType n (E.FuncType src id ts) =
   let (n',ps,ts') = rmAFDTypes n ts
       newVar      = E.VarType (makeNewId src n')
       p           = E.Pred src id (addTypeToTail ts' newVar)
   in (n'+1,p:ps,newVar)
rmAFDType n primType = (n,[],primType)

rmAFDTypes :: Int -> [E.Type] -> (Int,[E.Pred],[E.Type])
rmAFDTypes n (t:ts) = 
   let (n',p1,t')   = rmAFDType n t
       (n'',p2,ts') = rmAFDTypes n' ts
   in (n'',p1++p2,t':ts')
rmAFDTypes n []     = (n,[],[])

rmAFDCtxt :: Int -> E.Ctxt -> (Int,E.Ctxt)
rmAFDCtxt n (E.Ctxt ps) = 
   let (n',ps') = rmAFDPreds n ps
   in (n',E.Ctxt ps')

rmAFDPreds :: Int -> [E.Pred] -> (Int,[E.Pred])
rmAFDPreds n (p:ps) =
    let (n',p')   = rmAFDPred n p
        (n'',ps') = rmAFDPreds n' ps
    in (n'',p'++ps')
rmAFDPreds n [] = (n,[])

rmAFDPred :: Int -> E.Pred -> (Int,[E.Pred])
rmAFDPred n (E.Pred src id ts) =
    let (n',ps,ts') = rmAFDTypes n ts
    in (n',(E.Pred src id ts'):ps)

rmAFDClass :: E.Class -> (E.Class,[E.Dec])
rmAFDClass (E.Class ctxt pred fd wh) = ((E.Class ctxt pred fd wh),[])
rmAFDClass (E.AFDClass ctxt pred fd afd wh) = 
   let (decs,atIds) = rmAFDAFDDecs afd
       wh'          = rmAFDClassWhere atIds wh
   in (E.Class ctxt pred fd wh',decs)

rmAFDAFDDecs :: [E.AFDDec] -> ([E.Dec],[IdStr])
rmAFDAFDDecs ((AFDDec src id1 ids id2):decs) =
   let (decs',ids') = rmAFDAFDDecs decs
       id0            = makeNewId src 0
       clsDec         = makeClassDec src id1 (addIdToTail ids id0)
       funcRule       = makeFuncRule src id1 ids
   in (clsDec:funcRule:decs',(idStr id1):ids') --(makePred src id1 (addIdToTail ids id2)):preds')
   where
      makeClassDec :: SrcInfo -> Id -> [Id] -> E.Dec
      makeClassDec src id ids =
         let p = makePred src id ids
         in E.ClassDec src (E.Class E.emptyCtxt p [] [])
      makeFuncRule :: SrcInfo -> Id -> [Id] -> E.Dec
      makeFuncRule src id ids =
         let id1 = makeNewId src 1
             id2 = makeNewId src 2
             p1  = makePred src id (addIdToTail ids id1)
             p2  = makePred src id (addIdToTail ids id2)
             eq  = E.EqPrim src (E.VarType id1) (E.VarType id2)
         in E.RuleDec src (E.PropRule (E.Ctxt (p1:[p2])) (E.Cnst [eq]))
rmAFDAFDDecs [] = ([],[])

rmAFDClassWhere :: [IdStr] -> [E.Dec] -> [E.Dec]
rmAFDClassWhere atIds (d:ds) = 
   let ds' = rmAFDClassWhere atIds ds
       c   = rmAFDDec (identifyATs atIds d)
   in case c of
       [c'] -> c':ds'
       _    -> error "Error in rmAFDClassWhere"
rmAFDClassWhere _ [] = []

-- This function unfolds type constructor applications (E.AppType), intended to be
-- type functions (E.FuncType). ie. if we have the class declaration, 
-- class TC a b where
--    type F1 a b
--    f :: a -> a -> F1 a b
-- The parser will parse F1 a b as a function application ((F1 a) b), which we must unfold
-- to E.FuncType F1 [a,b].
identifyATs :: [IdStr] -> E.Dec -> E.Dec       
identifyATs atIds (E.AnnDec src sig) =
   let (E.Sig id ann tschm) = sig
       (E.TSchm ctxt ty) = tschm
       ty' = idATs atIds ty
   in (E.AnnDec src (E.Sig id ann (E.TSchm ctxt ty')))
identifyATs _ _ = error "Error in rmAFDClassWhere"

idATsCtxt :: [IdStr] -> E.Ctxt -> E.Ctxt
idATsCtxt ids (E.Ctxt ps) = let ps' = map (idATsPred ids) ps
                            in (E.Ctxt ps')

idATsPred :: [IdStr] -> E.Pred -> E.Pred
idATsPred ids (E.Pred src id ts) = 
      let ts' = map (idATs ids) ts
      in (E.Pred src id ts')

idATs :: [IdStr] -> E.Type -> E.Type
idATs atIds (E.AppType src t1 t2) =
          let t2' = idATs atIds t2
          in case (idATs atIds t1) of
               (E.FuncType src' id ts) -> E.FuncType src id (addTypeToTail ts t2')
               (E.ConType id)          -> let mb = findIndex (==(idStr id)) atIds
                                          in case mb of
                                               Nothing -> E.AppType src (E.ConType id) t2'
                                               _       -> E.FuncType src id [t2']
               t1'                     -> E.AppType src t1' t2'
idATs atIds (E.ArrType src t1 t2) =
          let t1' = idATs atIds t1
              t2' = idATs atIds t2
          in E.ArrType src t1' t2'
idATs atIds (E.TupType src ts) =
          let ts' = map (idATs atIds) ts
          in E.TupType src ts'
idATs atIds (E.ListType src t) =
          E.ListType src (idATs atIds t)
idATs atIds (E.UnionType src ts) =
          let ts' = map (idATs atIds) ts
          in E.UnionType src ts'
idATs atIds (E.StarType src t) =
          E.StarType src (idATs atIds t)
idATs atIds (E.OptionType src t) =
          E.OptionType src (idATs atIds t)
idATs atIds (E.AnnType src id t) =
          E.AnnType src id (idATs atIds t)
idATs atIds (E.ConType id) = 
          let mb = findIndex (==(idStr id)) atIds
          in case mb of
               Nothing -> E.ConType id
               _       -> E.FuncType (idSrcInfo id) id []
idATs atIds t = t 


rmAFDInst :: E.Inst -> (E.Inst,[E.Dec])
rmAFDInst (E.Inst ctxt pred wh) = (E.Inst ctxt pred wh,[])
rmAFDInst (E.AFDInst ctxt pred adefs wh) =
   let ids       = collectAFDIds adefs
       decs      = rmAFDAFDDefs ids adefs
       wh'       = rmAFDDecs wh
       (_,ctxt') = rmAFDCtxt 0 (idATsCtxt ids ctxt)
   in (E.Inst ctxt' pred wh',decs)
   where
      collectAFDIds :: [E.AFDDef] -> [IdStr]
      collectAFDIds (a:as) =
         let (E.AFDDef src id _ _) = a
         in (idStr id):(collectAFDIds as)
      collectAFDIds [] = []

rmAFDAFDDefs :: [IdStr] -> [E.AFDDef] -> [E.Dec]
rmAFDAFDDefs ids (a:as) =
   let (E.AFDDef src id ts t) = a
       t'         = E.VarType (makeNewId src 1)
       ts'        = addTypeToTail ts t'
       p          = E.Pred src id ts'
       (_,ps,t'') = rmAFDType 2 (idATs ids t) 
       ps'        = map (E.PredPrim) ps
       eq         = E.EqPrim src t' t''
       decs       = rmAFDAFDDefs ids as
   in (E.RuleDec src (E.SimpRule (E.Ctxt [p]) (E.Cnst (eq:ps')))):decs
rmAFDAFDDefs _  [] = []

------------------------------
-- Auxilliary functions supporting AFD translation process

idsToVars :: [Id] -> [E.Type]
idsToVars (id:ids) = (E.VarType id):(idsToVars ids)
idsToVars []       = []

addIdToTail :: [Id] -> Id -> [Id]
addIdToTail (id:ids) id' = id:(addIdToTail ids id')
addIdToTail [] id'       = [id']

addTypeToTail :: [E.Type] -> E.Type -> [E.Type]
addTypeToTail (t:ts) t' = t:(addTypeToTail ts t')
addTypeToTail [] t'       = [t']

makePred :: SrcInfo -> Id -> [Id] -> E.Pred
makePred src id ids = E.Pred src id (idsToVars ids)

makeNewId :: SrcInfo -> Int -> Id
makeNewId src n = let str = "!v_" ++ (show n)
                  in mkId src str

addToSig :: E.Sig -> [E.Pred] -> E.Sig
addToSig (E.Sig id ann tschm) ps =
   let (E.TSchm ctxt ty) = tschm
       (E.Ctxt ps')      = ctxt
       ctxt'             = E.Ctxt (ps ++ ps')
   in E.Sig id ann (E.TSchm ctxt' ty)

mergeCtxt :: E.Ctxt -> E.Ctxt -> E.Ctxt
mergeCtxt (E.Ctxt ps1) (E.Ctxt ps2) = E.Ctxt (ps1 ++ ps2)
