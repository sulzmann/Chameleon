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
-- W-based type inference scheme.
--
-------------------------------------------------------------------------------

module Core.Inference (
    typeInference
) where 

import Char
import List
import Maybe
import Monad
import System
import IO

import Misc
import Misc.Error
import Misc.Result
import Misc.ErrorMsg
import Core.Name
import Core.CHR
import Core.Types
import Core.Constraint
import Core.Justify
import Core.BuiltIn
import Core.InfGoal
import Core.InfResult
import Core.Solver

import AST.SrcInfo
import AST.CallGraph
import qualified AST.Internal as AST

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- the TR (translation) monad

-- NOTE: `topVs' are the variables representing types of :: annotated values,
-- i.e. these are the variables we check to see if any `existential' var
-- escapes through.
data State = St { num :: Int,		    -- unique number store	
		  chrs :: [CHR],	    -- generated CHRs
		  sccs :: [SCC],	    -- strongly connected components
		  topVs :: [Var],	    -- top vars
		  locinfo :: LocInfo,	    -- classifies locations
		  matches :: Matches,	    -- ucons matches
		  results :: [InfResult] }  -- inference results

----------------------------------------

newtype TR a = TR (State -> IO (SimpleResult (a,State)))

instance Monad TR where

    -- return :: a -> TR a
    return a = TR (\s -> return (mkSuccess (a,s)))

    -- (>>=)  :: TR a -> (a -> TR b) -> TR b
    (TR a) >>= f = TR (\s -> do r <- a s 
				case r of
				 Failure e b -> return (Failure e b)
				 Success e (a',s') -> do
				    let TR f' = f a' 
				    r' <- f' s'
				    return (r >> r'))

----------------------------------------

-- has a number supply
instance HasNumSupply TR where
    freshInt = next

-- can accumulate errors
instance AccumError TR where
    addErrorMsg  = addError

----------------------------------------

-- unpacks the translator
runTR :: TR a -> IO (SimpleResult a)
runTR tr = do
    res <- runTRAll tr
    return $ case res of
	Failure e b	-> Failure e b
	Success e (a,_) -> Success e a

runTRAll :: TR a -> IO (SimpleResult (a, State))
runTRAll (TR f) = f initState
  where 
    initState = St 0 [] [] [] emptyLocInfo [] []

----------------------------------------

doIO :: IO a -> TR a
doIO c = TR (\st -> c >>= \r -> return (mkSuccess (r, st)))

puts :: String -> TR ()
puts = doIO . putStrLn

----------------------------------------

-- functions for examining and updating the state
trGet f    = TR (\st -> return (mkSuccess (f st, st)))
trUpdate f = TR (\st -> return (mkSuccess ((), f st)))
trSet f x  = trUpdate $ f (const x)

num' f st     = st {num = f (num st)}
chrs' f st    = st {chrs = f (chrs st)}	
sccs' f st    = st {sccs = f (sccs st)}
topVs' f st   = st {topVs = f (topVs st)}
locinfo' f st = st {locinfo = f (locinfo st)}
results' f st = st {results = f (results st)}
matches' f st = st {matches = f (matches st)}

----------------------------------------
-- using the number store

getNum = trGet num
incNum = trUpdate $ num' (+1) 
setNum n = trUpdate $ num' (const n)

next = do n <- getNum
	  incNum
	  return n

----------------------------------------

-- adds a goal to the state
addResults :: [InfResult] -> TR ()
addResults res = trUpdate $ results' (res++)

getResults :: TR [InfResult]
getResults = trGet results

----------------------------------------

addMatches :: Matches -> TR ()
addMatches ms = trUpdate $ matches' (ms++)

----------------------------------------

pushTopV :: Var -> TR ()
pushTopV v = trUpdate $ topVs' (v:)

popTopVs :: Int -> TR ()
popTopVs n = trUpdate $ topVs' (drop n)

getAndClearTopVs :: TR [Var]
getAndClearTopVs = do 
    vs <- trGet topVs 
    trUpdate $ topVs' (const [])
    return vs

getTopVs :: TR [Var]
getTopVs = trGet topVs

----------------------------------------
-- accumulating error messages
    
addError :: HasSrcInfo a => a -> Msg -> TR ()
addError x m =
    let err = mkError (getSrcInfo x) m
    in  TR (\st -> return (Success [err] ((), st)))

----------------------------------------
-- making type variables

-- produce a new variable, of no particular location
newVar :: TR Type
newVar = do 
    n <- next
    let str = 'v' : show n
    return (TVar (mkVar str))
    
-- generate a new type variable annotated with the given location
newVarLoc :: Loc -> TR Type
newVarLoc l = do 
    n <- next
    let str = 'v' : show n
    return (TVar (mkLocVar str l))

-- generates a new type variable annotated with a complete source reference
-- takes the original variable name, and the source info.
newVarRef :: String -> SrcInfo -> TR Type
newVarRef id0 s = do
    n <- next
    let id1 = 'v' : show n
    return (TVar (mkRefVar id0 s id1))

-- generates n new type variables
newVars :: Int -> TR [Type]
newVars n = sequence (replicate n newVar)

--------------------------------------------------------------------------------
-- representation of results and environment

-- type, constraint pair (a `result')
type Res = (Type, Constraint)
nullRes  = (tupleType [], trueConstraint)

-- takes a type (or ucons) and converts it into a res.
typeRes :: Type -> Res
typeRes t = (t, trueConstraint)

-- converts a user constraint into a res.
uconRes :: UCons -> Res
uconRes uc = let t = head (ucTypes uc)
	     in  (t, toConstraint uc)

-- a result, possibly with some existential variables and constraints
-- first are the non-existential type and constraint, then a list of
-- existential variables, and finally constraints on those variables
type ERes = (Type, Constraint, [Var], Constraint) 

----------------------------------------

-- An inference context - used to accumulate the constraints and type imposed 
-- upon a program fragment by its context.
type InfContext = (Constraint, Type)

----------------------------------------

-- TSchm : type scheme with universal variables and constraint context
-- ETschm: as above, but with a separate list of `existential' variables 
--	   (the second list)
data TSchm = TSchm [Var] Constraint Type 
	   | ETSchm [Var] [Var] Constraint Type
    deriving (Show)

tschmToRes :: TSchm -> Res
tschmToRes (TSchm _ c t) = (t,c)
tschmToRes (ETSchm _ _ c t) = (t,c)

instance TypeOps TSchm where
    -- WARNING: apply does not respect the (implicit, universal) quantifier, 
    -- use applyTSchm for that.
    apply s ts = case ts of
		    TSchm vs c t -> TSchm (apply s vs) (apply s c) (apply s t)
		    ETSchm vs es c t -> ETSchm (apply s vs) (apply s es)
					       (apply s c) (apply s t)

    fv ts = case ts of
		TSchm vs c t -> fv (c,t) `without` vs
		ETSchm vs es c t -> fv (c,t) `without` (vs ++ es)

-- | First renames bound variables, then applies given substitution.
applyTSchm :: Subst -> TSchm -> TR TSchm
applyTSchm s ts = do
    ts' <- renameTSchm ts
    return (apply s ts')

-- | Renames a type scheme.
renameTSchm :: TSchm -> TR TSchm
renameTSchm ts = do
    rs <- renameSubst qvs
    return (apply rs ts)
  where
    qvs = case ts of
	    TSchm vs _ _ -> vs
	    ETSchm vs es _ _ -> vs ++ es

instance Pretty TSchm where
    pretty tschm = case tschm of
	TSchm vs c t -> pretty_vs vs ++ pretty_c c ++ pretty t
	ETSchm vs es c t -> pretty_vs (vs ++ es) ++ pretty_c c ++ pretty t
      where
	pretty_c c = if c == trueConstraint then "" else "("++pretty c++") => "
	pretty_vs vs = if null vs then "" else "forall " ++ pretty vs ++ ". "

-- replaces ugly-looking variable names in a (closed) type scheme
prettyRenameTSchm :: TSchm -> TSchm
prettyRenameTSchm = prettyRenameExplicitFV fv'
  where
    fv' ts = case ts of
		TSchm vs c t -> fv (c,t)
		ETSchm vs es c t -> fv (c,t)

mostGeneralTSchm :: TSchm
mostGeneralTSchm = TSchm [a] trueConstraint (TVar a)
  where
    a = mkVar "a"

mkSimpleTSchm :: Type -> Constraint -> TSchm
mkSimpleTSchm t c = TSchm (fv (c,t)) c t

typeToSimpleTSchm :: Type -> TSchm
typeToSimpleTSchm t = TSchm [] trueConstraint t

typeToUnivTSchm :: Type -> TSchm
typeToUnivTSchm t = TSchm (fv t) trueConstraint t

gen :: TypeOps a => a -> Type -> Constraint -> TSchm
gen env t c = TSchm vs c t
  where
    vs = fv t `without` fv env

-- NOTE: we keep data constructors distinct from functions (let-bound things)
--	 since we need to keep track of any existential variables/constraints
data VarRes = Var  { varResId :: IdStr,		    -- id
		     varResTSchm :: TSchm }	    -- type scheme

	    | DCon { varResId :: IdStr,		    -- data constructor
		     varResTSchm :: TSchm }	    -- type scheme
    deriving Show

-- NOTE: see the warning about renaming type schemes, at the instance of
-- TypeOps for TSchm.
instance TypeOps VarRes where
    fv vr = fv (varResTSchm vr)
    apply s vr = vr { varResTSchm = apply s (varResTSchm vr) }

instance Pretty VarRes where
    pretty (Var id t)  = id ++ ":" ++ pretty t
    pretty (DCon id t) = id ++ ":" ++ pretty t 

-- NOTE: we only store the user constraint for the inference CHR in the
--	 environment, but the cons. for the annotation can be derived from it
--	 by mkAnnUC.
mkAnnUC :: UCons -> UCons
mkAnnUC (UC ps ts j) = 
    let ps' = mkFreeName (mkAnnIdStr (nameStr ps))
    in  UC ps' ts j

-- Constructor predicate names are extended with a ':k' suffix. (This is so
-- that they can be distinguished from type class constraints which otherwise
-- would have the same name.)
mkKonUC :: UCons -> UCons
mkKonUC (UC ps ts j) = 
    let ps' = mkFreeName (mkKonIdStr (nameStr ps))
    in  UC ps' ts j

--------------------------------------------------------------------------------
-- Bogus results - use these as placeholders in case of an error 
-- (just so that we can continue, and hopefully accumulate more errors)

bogusIdStr :: IdStr
bogusIdStr = "Bogus, man!"

bogusVar :: Var
bogusVar = mkVar bogusIdStr

bogusType :: Type
bogusType = TVar bogusVar

bogusUCons :: UCons
bogusUCons = UC (mkFreeName bogusIdStr) [] noJust

bogusConstraint :: Constraint
bogusConstraint = trueConstraint

bogusTSchm :: TSchm
bogusTSchm = TSchm [bogusVar] bogusConstraint bogusType

bogusRes :: Res
bogusRes = (bogusType, bogusConstraint)

bogusDCon :: VarRes 
bogusDCon = DCon bogusIdStr bogusTSchm

--------------------------------------------------------------------------------

type VarEnv = [VarRes]		    -- maps term variables to type/cons
type TypeEnv = [(IdStr, Var)]	    -- maps source vars to type vars
type PredEnv = [(IdStr, Name)]	    -- maps predicate symbols to Names

-- complete environment for constraint/CHR generation
data Env = Env { varEnv  :: VarEnv, 
		 typeEnv :: TypeEnv,
		 predEnv :: PredEnv }
    deriving Show

instance TypeOps Env where
    fv (Env v t _) = fv (v,t)
    apply s (Env v t p) = Env (apply s v) (apply s t) p

instance Pretty Env where
    pretty (Env v t p) = "v: " ++ pretty v ++ 
			 "\nt: " ++ pretty t ++ 
			 "\np: " ++ pretty p

emptyEnv = Env [] [] []

addEnv :: Env -> Env -> Env
addEnv (Env v1 t1 p1) (Env v2 t2 p2) = Env (v1++v2) (t1++t2) (p1++p2)

sumEnvs :: [Env] -> Env
sumEnvs es = foldl addEnv emptyEnv es

----------------------------------------
-- manipulating and looking up the environment

varEnv'  f env = env { varEnv = f (varEnv env) }
typeEnv' f env = env { typeEnv = f (typeEnv env) }
predEnv' f env = env { predEnv = f (predEnv env) }

extendVarEnv  env x = varEnv'  (x:) env
extendTypeEnv env x = typeEnv' (x:) env
extendPredEnv env x = predEnv' (x:) env
 
lookupVarEnv :: IdStr -> Env -> Maybe VarRes
lookupVarEnv id env = let xs = filter ((==id) . varResId) (varEnv env)
		      in  listToMaybe xs

lookupTypeEnv = lookupEnvGeneral typeEnv
lookupPredEnv = lookupEnvGeneral predEnv
lookupEnvGeneral p id env = lookup id (p env)

----------------------------------------
-- standard environment

trueDat :: Show a => a -> Env -> TR ()
trueDat a env = case lookupVarEnv "True" env of
		Nothing -> puts (show a ++ ") `True' missing")
		Just _  -> puts (show a ++ ") `True' present")

stdEnv = Env { varEnv  = [ miscDCon listStr listNullType,
			   miscDCon consStr listConsType,
			   miscDCon unitStr unitType,
			   miscDCon trueStr boolType,
			   miscDCon falseStr boolType ] ++ 
			   miscDCons [(tupleStr n,tupleConType n) | n<-[2..7]]++
			   miscDCons [(nListStr n,nListConType n) | n<-[1..7]],
	       typeEnv = [],
	       predEnv = [] }
  where
    miscDCon str t = DCon str (typeToUnivTSchm t)
    miscDCons = map (uncurry miscDCon)


listNullType = let a = TVar (mkVar "a")
	       in  listType a 

listConsType = let a = TVar (mkVar "a")
	       in  a `arrow` (listType a `arrow` listType a)

--------------------------------------------------------------------------------
-- miscellaneous utility functions

-- returns a constraint enforcing all given types as equal
eqList :: Just -> [Type] -> Constraint
eqList j ts = toConstraint [ (t1 =+= t2) j | (t1, t2) <- zip ts (tail ts) ]

-- unifies all elements of the list with t
listEq :: Just -> Type -> [Type] -> Constraint
listEq j t1 ts = toConstraint [ (t1 =+= t2) j | t2 <- ts ]

mkAnnId :: AST.Id -> AST.Id
mkAnnId id = id { AST.idStr = AST.idStr id ++ ":a" }

-- turns a function identifier string into one that refers to an annotation
mkAnnIdStr :: IdStr -> IdStr
mkAnnIdStr = (++":a")

-- tests if the identifier string refers to an annotation
isAnnIdStr :: IdStr -> Bool
isAnnIdStr id = case reverse id of
		    ('a':':':cs) -> True
		    _ -> False

-- Use this to extend the names of data constructor predicates. 
mkKonIdStr :: IdStr -> IdStr
mkKonIdStr = (++":k")

predId :: IdStr -> IdStr
predId ""     = error "CHRGenerator.predId"
predId (c:cs) = toUpper c : cs

--------------------------------------------------------------------------------
-- top-level environment initialisation

-- Do all the top-level initialisation:
--  - data decs
--  - rule decs
--  - classes
--  - instances
-- First list of decs is local to the current module, second are imported.
initTopEnv :: Env -> [AST.Dec] -> [AST.Dec] -> TR (Env, [CHR])
initTopEnv env ds ds_imp = do
    let ds' = ds_imp ++ ds 
    env1 <- initDataDecs env ds'
    env2 <- initPrimDecs (env1 `addEnv` env) ds'
    (env3, chrs_class) <- initClassDecs env2 ds'
    chrs_inst	       <- initInstDecs env3 ds ds_imp
    (env4, chrs_rule)  <- initRuleDecs env3 ds'
    return (env4, chrs_rule ++ chrs_class ++ chrs_inst)

----------------------------------------

-- process data declarations
initDataDecs :: Env -> [AST.Dec] -> TR Env
initDataDecs env ds0 = do
    let ds = dataDecs ds0
    env1 <- initDatCons env ds
    return env1
  where
    -- filters out non-DataDecs
    dataDecs :: [AST.Dec] -> [AST.Dec]
    dataDecs = filter isDataDec

    isDataDec (AST.DataDec {}) = True
    isDataDec _ = False

    dataType (AST.DataDec _ dt _) = dt


-- Takes current environment and a list of data declarations, and returns a new
-- environment with updated venv to include new data constructors.
initDatCons :: Env -> [AST.Dec] -> TR Env
initDatCons env cs = do
    envs <- mapM (initDatCon env) cs
    return (sumEnvs envs)

-- Add variables bound by the data dec. to the environment, and translate each
-- data constructor.
initDatCon :: Env -> AST.Dec -> TR Env
initDatCon env (AST.DataDec _ (AST.DataType id ts) cs) = do 
    vs <- newVars (length ts)
    let trs  = zip (map (AST.idStr . varTypeId) ts) (map fromTVar vs)
	con  = mkTCon id
	t    = foldl TApp con vs
	env' = foldl extendTypeEnv env trs
    envs <- mapM (initCon t env') cs
    return (sumEnvs envs)
  where
    varTypeId (AST.VarType id) = id
    varTypeId _ = bug "non-var type in new data type declaration"

initCon :: Type -> Env -> AST.Cons -> TR Env
initCon t_res env (AST.Cons s vs c (AST.DataType id ts)) = do
    -- extend the environment with the exist. vars
    let vs' = map AST.VarType vs
    v_res <- mapM (consTypeNew emptyEnv) vs'

    -- the new environment, and type variables
    let (env', v_tvs) =  let (v_envs, rss) = unzip v_res
			     v_env = sumEnvs v_envs
			     -- the exist. variables
			     tvs = let (ts,_) = unzip rss
				   in  map fromTVar ts
			 in  (v_env `addEnv` env, tvs)
   
    -- generate user constraints from the context
    (_, c_ctxt) <- consCnst env' c

    t' <- newVar
    etcs <- consTypesCur env' ts 
    let j    = getSrcLoc id
	ts   = map fst (snd etcs)
	t    = foldr arrow t_res ts
	str  = AST.idStr id
	nm   = mkName str (getSrcInfo id) str
	uc   = mkKonUC (njUC nm [t']  `withJust` j)
	c_rhs  = (t' =:= t) `withJust` j /\ c_ctxt
	dcInfo = HMRule 
	chr    = SimpRule dcInfo [uc] c_rhs
	v    = DCon str (ETSchm (fv (c_ctxt,t) `without` v_tvs) v_tvs c_ctxt t)
	env''  = extendVarEnv emptyEnv v
   
    return env''


----------------------------------------
-- process rule declarations

-- converts a list of rule declarations into CHR rules
initRuleDecs :: Env -> [AST.Dec] -> TR (Env, [CHR])
initRuleDecs env ds = do
    let rs = filter isRuleDec ds
    genRules env rs
  where
    isRuleDec (AST.RuleDec {}) = True
    isRuleDec _ = False

-- NOTE: Decs are all RuleDecs at this point
genRules :: Env -> [AST.Dec] -> TR (Env, [CHR])
genRules = procMany genRule

genRule :: Env -> AST.Dec -> TR (Env, CHR)
genRule env d@(AST.RuleDec s r) = case r of
    AST.SimpRule ctxt cnst -> do
	    (env1, c1) <- consCtxt env  ctxt
	    (env2, c2) <- consCnst env1 cnst
	    let info = ConsRule
	        chr  = SimpRule info (cUCons c1) c2
	        env3 = env {predEnv = predEnv env2}
	    return (env3, chr)

    AST.PropRule ctxt cnst -> do
	    (env1, c1) <- consCtxt env ctxt
	    (env2, c2) <- consCnst env1 cnst
	    let info = ConsRule
	        chr  = PropRule info (cUCons c1) c2
	        env3 = env {predEnv = predEnv env2}
	    return (env3, chr)
	    
  where
    l = getSrcLoc d
    j = locToJust l


----------------------------------------
-- process class declarations

-- generates CHR rules from class declarations 
-- (including F.D. improvement rules)
initClassDecs :: Env -> [AST.Dec] -> TR (Env, [CHR])
initClassDecs env ds = do
    let cs = filter isClassDec ds
	is = filter isInstDec ds
    initClasses env ds cs
  where
    isClassDec (AST.ClassDec {}) = True
    isClassDec _ = False

    isInstDec (AST.InstDec {}) = True
    isInstDec _ = False

-- first list of declarations contains only instances, second is all classes
initClasses :: Env -> [AST.Dec] -> [AST.Dec] -> TR (Env, [CHR])
initClasses env is ds = do 
    (env',chrss) <- procMany (initClass is) env ds
    return (env', concat chrss)

-- Given a list of instance declarations, and an environment, generates the
-- CHRs for the class declaration passed as the third argument. This includes
-- *all* the F.D. rules associated with this class (and all instances of it.)
initClass :: [AST.Dec] -> Env -> AST.Dec -> TR (Env, [CHR])
initClass is env (AST.ClassDec s (AST.Class ctxt p fds w)) = do
    -- first the sub-class CHR
    (env1, uc) <- consPred env p
    (env2, c)  <- consCtxt env1 ctxt
    let chr_sub = let info = ConsRule
		  in  PropRule info [uc] c
    -- now the method rules
    env3 <- chrMethods env2 uc w
    let env4 = env3 { typeEnv = typeEnv env }	-- don't let out any type vars
    -- finally the F.D. rules
    chrs_fds <- mapM (initFunDep env2 is) (zip (repeat uc) fds)
    return (env4, chr_sub : concat chrs_fds)

chrMethods :: Env -> UCons -> [AST.Method] -> TR Env
chrMethods env uc ms = do
    vs <- mapM chrMethod ms
    let env' = foldl extendVarEnv env vs 
    return env'
  where
    chrMethod :: AST.Method -> TR VarRes
    chrMethod (AST.Method id ts) = do
	(_env', (t_t, c_t)) <- consNewTSchm env ts
	let ts = mkSimpleTSchm t_t (uc /\ c_t)
	    v  = Var (AST.idStr id) ts
	return v
	    
-- classification of instance variables
data InstVar = InDomain
	     | InRange
	     | InNeither
    deriving Eq

-- Generates all the F.D. rules for the given environment and instance list.
initFunDep :: Env -> [AST.Dec] -> (UCons, AST.FunDep) -> TR [CHR]
initFunDep env is (uc@(UC nm ts _), AST.FunDep s d r) = do
    let vs_d = map (idToType . AST.idStr) d
        vs_r = map (idToType . AST.idStr) r
    -- first the simple, multi-headed rule
    chr_fd <- do phi <- renameSubst vs_r
		 rho <- renameSubst (fv uc `without` fv (vs_d ++ vs_r))
		 let ucs  = [uc, apply (rho `composeSubst` phi) uc]
		     eqs  = [ (t =:= t') `withJustOf` s | t <- ts, 
					let t' = apply phi t, t /= t' ]
		     info = ConsRule
		 return (PropRule info ucs (toConstraint eqs))
    
    -- now the improvement rules (find all matching instances)
    -- first, record the position of domain and range variables in the pred.
    let cls = [ c | t <- ts, let c | t `elem` vs_d = InDomain
				   | t `elem` vs_r = InRange
				   | otherwise	   = InNeither ]
	ps  = [ (p,s) | (AST.InstDec s (AST.Inst _ p@(AST.Pred _ id _) _))<- is,
			AST.idStr id == nameStr nm ]
    imps <- mapM (mkImp cls s) ps 
    return (chr_fd:imps)
  where
    -- generate improvement rule 
    -- we pass in the location of both the FD (1st) and the instance (2nd)
    mkImp :: [InstVar] -> SrcInfo -> (AST.Pred, SrcInfo) -> TR CHR
    mkImp bs s1 (p,s2) = do 
	(_, uc@(UC n ts j_uc)) <- consPred env p
	(ts', eqs) <- rep [] bs ts
	let uc'  = UC n ts' j_uc
	    eqs' = eqs `withJustOf` (s1,s2)
	    info = ConsRule
	    chr  = PropRule info [uc'] (toConstraint eqs')
	return chr
      where
	-- replace range variables by fresh variables
	rep :: [BCons] -> [InstVar] -> [Type] -> TR ([Type], [BCons])
	rep eqs [] ts = return (ts, eqs)
	rep eqs (c:cs) (t:ts) 
	    | c == InRange = do (ts', eqs') <- rep eqs cs ts
				v <- newVar
			        let eq = v =:= t
			        return (v:ts', eq:eqs')
				
	    | c == InNeither = do (ts', eqs') <- rep eqs cs ts
				  v <- newVar
				  return (v:ts', eqs')
	    
	    | otherwise    = do (ts', eqs') <- rep eqs cs ts
			        return (t:ts', eqs')
  
    -- map variables to types
    idToType :: IdStr -> Type 
    idToType id = case lookupTypeEnv id env of
	Just t -> TVar t
	_ -> bug ("FD variable `" ++ id ++ "' is unbound!" ++ 
		  "\nin env: " ++ show env)


----------------------------------------
-- process instance declarations

-- generates CHR rules from instance declarations
-- NOTE: we keep imported decs separate since we only want the imported classes
initInstDecs :: Env -> [AST.Dec] -> [AST.Dec] -> TR [CHR]
initInstDecs env ds ds_imp = do
    let is = filter isInstDec ds
	cs = filter isClassDec (ds ++ ds_imp)
    initInsts env cs is
  where
    isInstDec (AST.InstDec {}) = True
    isInstDec _ = False

    isClassDec (AST.ClassDec {}) = True
    isClassDec _ = False


-- first list of declarations contains only classes, second is all instances
initInsts :: Env -> [AST.Dec] -> [AST.Dec] -> TR [CHR]
initInsts env cs is = do 
    let cis = map getClass pis
    chrs <- concatMapM (initInst env) cis
    return chrs
  where
    -- classes and instances paired with their class pred. name
    pcs = [ (AST.idStr id, c) | 
	    c@(AST.ClassDec _ (AST.Class _ (AST.Pred _ id _) _ _)) <- cs ]
    pis = [ (AST.idStr id, i) | 
	    i@(AST.InstDec _ (AST.Inst _ (AST.Pred _ id _) _)) <- is ]

    -- pair instances with their classes, using above
    getClass :: (String, AST.Dec) -> (AST.Dec, AST.Dec)
    getClass (id, i) = case lookup id pcs of
	Just c  -> (c, i)
	Nothing -> bug ("initInsts: instance of undefined class: " ++ show i)


-- Generates all rules for the given instance declaration.
-- First dec is the class, second is the specific instance we're translating.
initInst :: Env -> (AST.Dec, AST.Dec) -> TR [CHR]
initInst env (AST.ClassDec _ cls@(AST.Class c1 p1 fds ms), 
	      AST.InstDec  s inst@(AST.Inst c2 p2 w)) = do
    (env1, ucc) <- consPred env p1	-- NOTE: variables in class dec. 
					-- shouldn't scope over instances
    (env2, uci) <- consPred env  p2
    (env3, c)   <- consCtxt env2 c2
    let chr = let info = ConsRule
	      in  SimpRule info [uci] c

    -- generate CHRs from methods
    let dms = match inst
    mapM_ (chrMethods env1 env3 c (ucc,uci)) dms
    return [chr]

  where
    -- Generate CHRs from the given instance method dec., and a subsumption
    -- check against the method definition (from the class.)
    -- We also pass in the class and instance dec. class predicates.
    -- NOTE: cenv -- environment used to translate the class dec. pred
    --	      env -- environment used for the instance dec. (contains type
    --		     variables from the instance Pred.)
    chrMethods :: Env -> Env -> Constraint -> (UCons,UCons) -> 
		  (AST.Dec, AST.Method) -> TR ()
    chrMethods cenv env c_ctxt (uc1,uc2) (d0, m) = do
	-- generate a new id for this method (so that it has a distinct
	-- predicate symbol)
	n1 <- freshInt
	let n2 = -- getSrcLoc d0
		 srcRow (getSrcInfo d0)
	    str = AST.idStr (valId d0) ++ "-" ++ show n1 ++ ":" ++ show n2 
	    (id,d) = case d0 of
		    AST.ValDec s1 (AST.LetBnd s2 id0 e) -> 
			let id = id0 {AST.idStr = str}
			in  (id, AST.ValDec s1 (AST.LetBnd s2 id e))

		    AST.ValDec s1 (AST.LetBndAnn s2 id0 at ts e) ->
			let id = id0 {AST.idStr = str}
			in  (id, AST.ValDec s1 (AST.LetBndAnn s2 id at ts e))

	-- generate types and constraints from the method def.
	-- NOTE: We don't want type variables in a classes method definitions
	--	 to scope over instances.
	(env1, (t_m,c_m)) <- consMethod cenv m 
	-- FIXME: We need to solve the subsumption constraint here
	return ()
	
{-	
	(env2, chrs)   <- chrTopDecs env [d]
	vvec <- typeVarVecClosed env
	-- generate the subsumption goal
	let uc   = lookupUC env2 str
	    tlv@[t,l,v] = ucTypes uc
	    vs   = nub (fv (t_m,c_m))
	    c_ts = let ts1 = ucTypes uc1
		       ts2 = ucTypes uc2
		   in  zipWith (=:=) ts1 ts2
	    lhs  = t =:= t_m /\ l =:= vnilType /\ v =:= vvec /\ 
		   c_ts /\ c_m /\ c_ctxt
	    sub  = IC vs (cUCons lhs, cBCons lhs) ([uc],[],[]) noJust
	    goal = (SubGoal id (map fromTVar tlv) (toConstraint sub))
-}	    
	-- let goal = error "goal 1"
	-- addGoal goal 
	-- return chrs
  
      where
	consMethod :: Env -> AST.Method -> TR (Env, Res)
	consMethod env (AST.Method id ts) = consNewTSchm env ts
	    
  
    -- match each instance method with its class definition
    match :: AST.Inst -> [(AST.Dec, AST.Method)]
    match (AST.Inst _ p w) = map find w 
      where
	find d = case lookup (AST.idStr (valId d)) idms of
		    Just m  -> (d,m)
		    Nothing -> bug ("initInst: no matching class method: " ++
				    show p ++ 
				    "\nd:\n" ++ show d ++ 
				    "\nms: \n" ++ showlist ms)
      
	idms = [ (methId m, m) | m <- ms ]
      
	methId (AST.Method id _) = AST.idStr id
      
    valId (AST.ValDec _ (AST.LetBnd _ id _))	    = id
    valId (AST.ValDec _ (AST.LetBndAnn _ id _ _ _)) = id
    valId _ = bug "initInst: non-ValDec as instance method"


----------------------------------------
-- process primitive declarations

initPrimDecs :: Env -> [AST.Dec] -> TR Env
initPrimDecs env ds = do
    let idts = [(AST.idStr id, ts) | AST.PrimDec _ (AST.Prim id str ts) <- ds]
    ers <- mapM (consTSchm env . snd) idts
    let (_, rs) = unzip ers
	ts   = [ TSchm (fv tc) c t | tc@(t,c) <- rs ]
	strs = map fst idts
	vs   = zipWith Var strs ts
        env' = foldl extendVarEnv env vs
    return env'


--------------------------------------------------------------------------------
-- environment initialisation for values

-- Initialise the environment with entries for let bindings.
initEnv :: Env -> [AST.LetBnd] -> TR Env
initEnv env lbs = foldM init env lbs
  where
    init env lb = case lb of 
	AST.LetBnd s id e -> do
	    t <- newVar
	    let v = Var (AST.idStr id) (typeToSimpleTSchm t)
	    return (extendVarEnv env v)
	    
	-- same as the LetBnd case
	AST.LetBndAnn s id AST.Exist ts e ->
	    let lb = AST.LetBnd s id e
	    in  init env lb
	
	AST.LetBndAnn s id AST.Univ ts e -> do
	    (env',(t,c)) <- consTSchm env ts
	    let ts = gen env t c
		v = Var (AST.idStr id) ts
	    return (extendVarEnv env' v)


mkIdName :: Bool -> AST.Id -> Name
mkIdName True  = mkTopName
mkIdName False = mkNestedName

-- Makes a name for a top-level id.
mkTopName :: AST.Id -> Name
mkTopName id = let str = AST.idStr id
	       in  mkName str (getSrcInfo id) str

-- Makes a name from an id. that's declared in some nested scope.
-- i.e. not at the top-level!
mkNestedName :: AST.Id -> Name
mkNestedName id = let str  = AST.idStr id
		      str' = str ++ ":" ++ show (getSrcLoc id)
		  in  mkName str (getSrcInfo id) str'
    
--------------------------------------------------------------------------------
-- Constraint generation

-- Takes an initial environment (\Gamma, V), a program to type, and a list of
-- imported declarations, and returns a list of inference results and a Boolean
-- value which indicates success.
inferenceTopLevel :: Env -> AST.Prog -> [AST.Dec] -> TR ([InfResult], Bool)
inferenceTopLevel env (AST.Prog ms) ds_imp = do
    let ds  = concatMap AST.moduleDecs ms
    (env', init_chrs) <- initTopEnv env ds ds_imp
    trSet chrs' init_chrs
    let lbs = [ lb | AST.ValDec _ lb <- ds ]
    -- type all top-level let binds
    a <- newVar
    (_, c) <- consLetBnds env' (trueConstraint,a) True lbs
    res1 <- getResults	    -- get other results
    -- if inference has already failed at least once, don't bother with any
    -- remaining subsumption constraints.
    if any Core.InfResult.isFailure res1 
      then do
	puts "!!! inference failure detected at top level\n"
	return (res1, False)
      else do -- solve any remaining constraints (subsumption)
	top_vs <- getTopVs 
	linfo  <- trGet locinfo
	(res2,_,ms)<-doIO (solveTypingConstraint init_chrs [] [] top_vs linfo c)
	addMatches ms
	let res = res1 ++ res2
	return (res, all isInfSuccess res)
    
----------------------------------------

-- takes a constraint generation function for a program fragment a, and returns
-- a function for a list of `a's, threading the environment through each call

procMany :: (Env -> a -> TR (Env, b)) -> Env -> [a] -> TR (Env, [b])
procMany = thread 

----------------------------------------
-- translating literals

consLit :: AST.Lit -> TR Res
consLit lit = case lit of 
    AST.IntegerLit {} -> return (typeRes integerType)
    AST.IntLit {}   -> return (typeRes intType)
    AST.FloatLit {} -> return (typeRes rationalType)
    AST.StrLit {}   -> return (typeRes stringType)
    AST.CharLit {}  -> return (typeRes charType)


----------------------------------------

-- Handles a let binding group.
consLetBnds :: Env -> InfContext -> Bool -> [AST.LetBnd] -> TR (Env, Constraint)
consLetBnds env ctxt top lbs = do
    sccs <- trGet sccs
    let lbss = filter (not . null) (orderLBs sccs lbs)
    (env', cs) <- procMany procLBs env lbss
    return (env', andList cs)
  where
    procLBs :: Env -> [AST.LetBnd] -> TR (Env, Constraint)
    procLBs env lbs = do
	env' <- initEnv env lbs
	consLetBndSCC env' ctxt top lbs
  
    -- order let bindings by (already-sorted) SCCs
    orderLBs :: [SCC] -> [AST.LetBnd] -> [[AST.LetBnd]]
    orderLBs [] _ = []
    orderLBs (scc:sccs) lbs = 
	[ lb | lb <- lbs, AST.idStr (AST.letBndId lb) `elem` scc' ] : 
	orderLBs sccs lbs
      where
	scc' = map AST.idStr scc


-- Generates and solves type constraints for the given set of let bindings,
-- representing all of the members of an SCC in this binding group.
consLetBndSCC :: Env -> InfContext -> Bool -> [AST.LetBnd] 
	      -> TR (Env, Constraint)
consLetBndSCC env ctxt@(c_ctxt, t_ctxt) top lbs = do
    -- find all constraints, c: to solve now, dc: to defer (float out)
    cdcs <- mapM (accumConstraints env) lbs
    let (cs,dcs) = unzip cdcs
    env' <- solve env (andList cs) lbs
    -- remove the topVs of the just-solved bindings
    popTopVs (length lbs)
    let cs' = dcs /\ cs	    
    return (env', cs')
  where
    accumConstraints :: Env -> AST.LetBnd -> TR (Constraint, Constraint)
    accumConstraints env lb = case lb of
	
	AST.LetBnd s id e -> do
	    a <- newVar
	    t <- newVarLoc (getSrcLoc s)
	    (t_e, c_e) <- consExp env (c_ctxt,a) e
	    pushTopV (fromTVar t)
	    case lookupVarEnv (AST.idStr id) env of
	      Nothing -> bug "Core.Inference.consLetBndSCC: id not in env!"
	      Just vr -> let (t',c') = tschmToRes (varResTSchm vr)
			     c'' = t =:= t_e /\ t =:= t' /\ c' /\ c_e
			 in  return (c'', trueConstraint)

	AST.LetBndAnn s id AST.Exist ts e -> do
	    a <- newVar
	    t <- newVarLoc (getSrcLoc s)
	    (env', (t_ts,c_ts)) <- consTSchm env ts
	    (t_e, c_e) <- consExp env' (c_ctxt /\ c_ts, a) e
	    pushTopV (fromTVar t)
	    case lookupVarEnv (AST.idStr id) env of
	      Nothing -> bug "Core.Inference.consLetBndSCC: id not in env!"
	      Just vr -> let (t',c') = tschmToRes (varResTSchm vr)
			     c'' = t =:= t_e /\ t =:= t' /\ t =:= t_ts /\ 
				   c_ts /\ c' /\ c_e 
			 in  return (c'', trueConstraint)

	AST.LetBndAnn s id AST.Univ ts e -> do
	    a <- newVar
	    t <- newVarLoc (getSrcLoc s)
	    (env', (t_ts, c_ts)) <- consNewTSchm env ts
	    (t_e, c_e) <- consExp env (c_ctxt /\ c_ts, a) e
	    -- only quantify over the local type variables (remove globals)
	    let vs  = nub (fv (t_ts,c_ts) `without` fv(typeEnv env))
		lhs = (t =+= t_e) s /\ (t =+= t_ts) s /\ c_ts
		sub = IC vs (cUCons lhs, cBCons lhs) 
			    (constraintToTuple c_e) noJust
	    pushTopV (fromTVar t)
--	    puts ("sub: " ++ pretty sub)
	    -- NOTE: We generate and add an inference result which gives the
	    -- value its annotated type. We do this here because the inference 
	    -- result, being the result of solving an implication, will either 
	    -- be True or False, and hence doesn't reflect the value's type at 
	    -- all.
	    -- This is safe because:
	    -- 1. If the implication is True, then this is the correct result.
	    -- 2. If the implication is False, then inference will fail and the
	    --    erroneous inference result won't be used anyway.
	    (_, (t_res, c_res)) <- consTSchm env' ts 
	    let res = InfSuccessW id t_res (cUCons c_res)
	    addResults [res]
	    return (trueConstraint, toConstraint sub)
	
    solve :: Env -> Constraint -> [AST.LetBnd] -> TR Env
    solve env c lbs = do
	tvs <- getTopVs
	-- puts ("solve, tvs: " ++ pretty tvs)
	let idvs = concatMap getTVs lbs
	    (ids,vs) = unzip idvs
	    
	-- puts ("env:\n" ++ pretty env)
	-- puts ("idvs:" ++ pretty idvs)
	-- puts ("c:\n" ++ pretty c)
	
	tss <- solveLet env top idvs c
	let vars = zipWith (Var . AST.idStr) ids tss
	    env' = foldl extendVarEnv env vars
	-- puts ("results: " ++ pretty vars ++ "\n")
	return env'
      where
	getTVs :: AST.LetBnd -> [(AST.Id,Var)]
	getTVs lb = case lb of
	    AST.LetBnd _ id _ -> [(id, getV id)]
	    AST.LetBndAnn _ id AST.Exist _ _ -> [(id, getV id)]
	    _ -> []
	  where
	    getV id = case lookupVarEnv (AST.idStr id) env of
			Nothing -> bug "Core.Inference.consLetBndSCC: lookup!"
			Just vr -> let (t',_) = tschmToRes (varResTSchm vr)
				   in  fromTVar t'


-- Takes the typing constraints representing the RHSs of a set of let bindings, 
-- solves the constraint, and build appropriate type schemes.
solveLet :: Env -> Bool -> [(AST.Id,Var)] -> Constraint -> TR [TSchm]
solveLet env top idvs c = do
    chrs <- trGet chrs
    -- We extract free variables from the env, then use the renamed types which
    -- we get back from the solver, for type scheme generalisation. 
    -- NOTE: We should exclude all of the temporary mono. variables in the
    -- environment, which belong to the current SCC. (otherwise we would never
    -- quantify over anything.)
    let free_vs = fv env `without` (map snd idvs)
    top_vs <- getTopVs 
    linfo  <- trGet locinfo
  
--  puts "solveLet: solveTypingConstraint"
    (res,ren_ts,ms) <- doIO (
			solveTypingConstraint chrs idvs free_vs top_vs linfo c)

--  puts ("res: " ++ pretty res)
    
    -- only save top-level results
    when top (addResults res)
    addMatches ms
    return (map (proc ren_ts) res)
  where
    proc :: [Type] -> InfResult -> TSchm
    proc ts res = case res of
	InfSuccessW id t ucs -> gen ts t (toConstraint ucs)

	-- NOTE: The failure will be discovered later when the results are
	-- examined, for now return a bogus, filler type scheme (forall a. a),
	-- so that we can continue.
	_ -> mostGeneralTSchm

----------------------------------------
-- translating expressions

consExps :: Env -> [(InfContext, AST.Exp)] -> TR [Res]
consExps env ces = do (_, rs) <- procMany gen env ces
		      return rs
  where
    gen env (ctxt,e) = do r <- consExp env ctxt e
		          return (env, r)

-- Generates types/constraints out of expressions.
-- Some typing rules, and their implementation (obviously) can be found below.
consExp :: Env -> InfContext -> AST.Exp -> TR Res
consExp env ctxt@(c_ctxt, t_ctxt) exp = case exp of
    -- NOTE: we don't bother generating constraints for internal functions
    --	     which are really just descriptive names for _|_
    --	     (e.g. "patternMatchFailed!")
    AST.VarExp id |  AST.idStr id == patternMatchFailedStr
		  || AST.idStr id == uninitialisedFieldStr
		  || AST.idStr id == noSuchFieldStr
		  || AST.idStr id == undefinedMethodStr -> do
	t <- newVar
	return (t, trueConstraint)
    
    AST.VarExp id -> do
	t <- newVarLoc l
	let mv = lookupVarEnv (AST.idStr id) env
	if isNothing mv 
	  then errVarUndefined id >> return bogusRes
	  else do
	    let ts = case fromJust mv of
			Var  _ ts -> ts
			DCon _ ts -> ts
	    ts' <- renameTSchm ts
	    let (t',c) = tschmToRes ts'
	    return (t, c_ctxt /\ (t =:= t_ctxt) /\
		       (t =+= t') j /\ reJust j c)
	
    -- we translate constructors as functions
    AST.ConExp id -> do
	t <- newVarLoc l
	let mv = lookupVarEnv (AST.idStr id) env
	if isNothing mv 
	  then errConUndefined id >> return bogusRes
	  else do
	    ts <- case fromJust mv of
		DCon _ ts -> renameTSchm ts
		Var  _ ts -> warn "Core.Inference.consExp: ConExp yields Var" 
				(renameTSchm ts)
	    let (t',c) = tschmToRes ts
	    return (t, c_ctxt /\ (t =:= t_ctxt) /\ 
		       (t =+= t') j /\ reJust j c)

    AST.LitExp i -> do
	(t, c) <- consLit i
	t' <- newVarLoc l
	return (t', c_ctxt /\ (t =:= t_ctxt) /\ 
		    (t' =+= t) j /\ c)

    AST.AppExp _ e1 e2 -> do
	a <- newVar
	b <- newVar
	let c = c_ctxt /\ (a =+= b `arrow` t_ctxt) j
	(t1, c1) <- consExp env (c,a) e1 
	(t2, c2) <- consExp env (c,b) e2 
	t3 <- newVarLoc l
	return (t3, t3 =:= t_ctxt /\ c1 /\ c2)

    AST.AbsExp _ id e -> do 
	-- NOTE: the pattern is a single variable -- it won't have any
	--	 context constraints, or exist. vars etc.
	(env', (t1, c1, _, _)) <- consPat env (AST.VarPat id)
	a <- newVar
	b <- newVar
	t <- newVarLoc l
	let ctxt' = (c_ctxt /\ a =:= t1 /\ 
		    (t =+= t_ctxt) j /\ t_ctxt =:= a `arrow` b, b)
	(t2, c2) <- consExp env' ctxt' e
	let c' = c1 /\ c2
        return (t, c')

    -- NOTE: remember that we allow matching over multiple expressions
    AST.CaseExp _ es ms -> do
	as <- newVars (length es)
	b  <- newVar
	let ctxts = zip (repeat c_ctxt) as
	r_e <- consExps env (zip ctxts es)
	let (t_es, c_es) = unzip r_e
	    ctxt' = (c_ctxt /\ b =:= foldr arrow t_ctxt as, b)
	r_ms <- consMatches env ctxt' ms
	t <- newVarLoc l
	let (t_ms, c_ms) = unzip r_ms
	    ft  = foldr arrow t t_es
	    eqs = listEq j ft t_ms
	return (t, c_es /\ eqs /\ c_ms)
	
    
    AST.LetExp s lbs e -> do 
	-- NOTE: The type component in the context for each let binding will
	-- get replaced by a fresh variable, so it is safe to pass the same one
	-- to each here. (see: consLetBnds)
	(env', c_lbs) <- consLetBnds env ctxt False lbs
        (t_e, c_e) <- consExp env' ctxt e
	t <- newVarLoc l
	return (t_e, (t =+= t_e) j /\ c_lbs /\ c_e)

  where
    l = getSrcLoc exp
    j = locToJust l

    envIds = map varResId (varEnv env)

    errVarUndefined id = addErrorMsg id (errorMsg id 
			    ["Undefined variable `" ++ AST.idOrigStr id ++ "'",
			     alternatives (AST.idStr id) envIds  ])
    
    errConUndefined id = addErrorMsg id (errorMsg id 
			    ["Undefined data constructor `"++ AST.idOrigStr id 
			     ++"'", alternatives (AST.idStr id) envIds ])
    
    errMalformedUCons uc = bug ("malformed user constraint `" ++ show uc ++ "'")


----------------------------------------
-- translating case matches

consMatches :: Env -> InfContext -> [AST.Match] -> TR [Res]
consMatches env ctxt = mapM (consMatch env ctxt)

-- returns the type of match as a function type, 
-- ie. t_pat1 -> ... -> t_patn -> t_res
--
-- ERROR REPORTING NOTE: We want the polymorphic variables in the implication to
-- refer to their pattern binding locations.
consMatch :: Env -> InfContext -> AST.Match -> TR Res
consMatch env ctxt@(c_ctxt, t_ctxt) m@(AST.Match ps e) = do
    (env', (rs, evs, ec)) <- consPatsAccum env ps
    let (t_ps, c_ps) = unzip rs
    as <- newVars (length ps)
    b  <- newVar
    let ctxt' = (c_ctxt /\ (t_ctxt =:= foldr arrow b as), b)
    (t_e, c_e) <- consExp env' ctxt' e
    t <- newVar
    let c = t =:= foldr arrow t_e t_ps
	c_rhs =  c_ps /\ c_e
        -- if there are no exist. variables and no context constraints, then 
        -- don't generate an implicatation
	c' | null evs && ec == trueConstraint = c /\ c_rhs
	   | otherwise = let left  = (cUCons ec, cBCons ec)
			     right = (cUCons c_rhs, cBCons c_rhs, cICons c_rhs)
                             ic    = IC evs left right noJust
                         in  ic /\ c
    return (t, c')

----------------------------------------
-- translating patterns

-- NOTES: patterns may contain existential variables


-- translates a list of patterns:
--  - the result is a list of corresponding type, constraint pairs, as well as
--    a list of all existential variables and a single, accumulated existential
--    constraint
consPatsAccum :: Env -> [AST.Pat] -> TR (Env, ([Res], [Var], Constraint))
consPatsAccum env ps = gen env [] [] trueConstraint ps
  where
    gen env rs etvs ec []  = return (env, (reverse rs, etvs, ec))
    gen env rs etvs ec (p:ps) = do
	(env', (t, c, etvs', ec')) <- consPat env p
	gen env' ((t,c):rs) (etvs' ++ etvs) (ec' /\ ec) ps
    
consPats = procMany consPat

consPat :: Env -> AST.Pat -> TR (Env, ERes)
consPat env pat = do
  x <- case pat of

    -- NOTE: If the pattern is '_', don't add it to the environment. 
    --	     i.e. we don't treat it as a variable.
    --
    {-----------------------------------------------------------
	
	    t_l, tx fresh
     --------------------------------------------------
	x_l |- (t_l | (t_l = tx)_l | env.{x:tx) 

    -----------------------------------------------------------}
    AST.VarPat id -> do 
	    tx <- newVar
	    tl <- newVarLoc l
	    let v = Var (AST.idStr id) (typeToSimpleTSchm tx)
		env' = extendVarEnv env v
	    return $ if AST.idStr id == "_"
	      then (env,  (tl, trueConstraint, [], trueConstraint))
	      else let c = toConstraint ((tl =+= tx) l)
		   in  (env', (tl, c, [], trueConstraint))

    AST.LitPat lt -> do 
	    (t_l, c_l) <- consLit lt
	    t <- newVarLoc l
	    let c = reJust j (t =:= t_l /\ c_l)
	    return (env, (t, c, [], trueConstraint))

    AST.ConPat s id aps ->
	case lookupVarEnv (AST.idStr id) env of
	  Nothing -> bug ("Core.Inference.consPat: undefined ConPat; " ++ 
			    show id ++ "\n" ++ unlines (map show (varEnv env)))
	  Just (DCon _ ts) -> do
	    ts' <- renameTSchm ts
	    let (_,evs1,ec1,t) = case ts' of
				  TSchm vs' c' t' -> (vs',[],c',t')
				  ETSchm vs' es' c' t' -> (vs',es',c',t')
	    eps@(env', (rs,evs2,ec2)) <- consPatsAccum env aps
	    t_res <- newVarLoc l
	    let (t_ps, c_ps) = unzip rs
	        t_con = foldr arrow t_res t_ps
		ec3  = ec2 /\ ec1
		evs3 = evs2 ++ evs1
		c    = (t =+= t_con) s /\ c_ps
	    -- return (env', (t_res,c,evs3,ec3))
	    return (env', (resultType t, c, evs3, ec3))
	  where
	    resultType (TApp t1 t2) | isArrowApp t1 = resultType t2
	    resultType t = t

	    isArrowApp (TApp t1 t2) = isArrow t1 
	    isArrowApp _ = False
	    isArrow (TCon n) = nameStr n == arrowStr
	    isArrow _ = False
	    
  let (_,(t,c,_,_)) = x
  -- puts ("pat:" ++ pretty pat ++ " : " ++ pretty (t,c))
  return x
  where
    l = getSrcLoc pat
    j = locToJust l


----------------------------------------
-- translating types (to internal format)

consTypeNew     = consType  (True,  False)
consTypeCur     = consType  (False, False)
consTypesNew    = consTypes (True,  False)
consTypesCur    = consTypes (False, False)
consTypeNewCons = consType  (True, True)
consTypeCurCons = consType  (False, True)


-- FLAGS:
--  1. if True, unbound variables can be added to the type environment if not 
--     there already, else their use results in failure
--  2. if True, return types as constraints, else just return the type directly
--     (constraint component can be discarded by caller)
consType :: (Bool, Bool) -> Env -> AST.Type -> TR (Env, Res)
consType fs@(fNew, fCons) env typ = case typ of

    AST.VarType id | str == "_" -> do 
			let id' = str ++ show (getSrcLoc id)
			t <- newVarRef str (getSrcInfo id) 
			return (env, (t, trueConstraint))
			    
		   | otherwise -> do 
			t' <- newVarRef str (getSrcInfo id)
			(env', t) <- getTVar env id
			let c_eq = toConstraint ((t' =+= t) j)
			return $ if fCons then (env', (t', c_eq))
					  else (env', (t, trueConstraint))
      where
	str = AST.idStr id

    AST.ConType id -> do 
	    t' <- newVarLoc l
	    -- If we don't care about this constructor being undefined 
	    -- (e.g. because its attached to something we imported), just
	    -- create a new type for it.
	    let t = mkTCon id
	        c_eq = toConstraint ((t' =+= t) j)
	    return $ if fCons then (env, (t', c_eq))
			      else (env, (t, trueConstraint))	


    -- Handle function arrow as a special case.
    -- (Never abstract it away into a constraint, as per ConTyps.)
    AST.AppType _ (AST.AppType _ (AST.ConType id) t1) t2 
	| AST.idStr id == "->" -> do
	    t' <- newVarLoc l
	    (env1, (t1', c1)) <- consType' env  t1
	    (env2, (t2', c2)) <- consType' env1 t2
	    let t_arr = mkTCon id
	        t    = TApp (TApp t_arr t1') t2'
		c_eq = (t' =+= t) j
		c    = c1 /\ c2
	    return $ if fCons then (env2, (t', c_eq /\ c))
			      else (env2, (t, c))

    AST.AppType _ t1 t2 -> do 
	    t' <- newVarLoc l
	    (env1, (t1', c1)) <- consType' env  t1
            (env2, (t2', c2)) <- consType' env1 t2
	    let t    = TApp t1' t2'
		c_eq = (t' =+= t) j
		c    = c1 /\ c2
	    return $ if fCons then (env2, (t', c_eq /\ c))
			      else (env2, (t, c))
  where
    s = getSrcInfo typ
    l = getSrcLoc typ
    j = locToJust l

    consType'  = consType fs
    consTypes' = consTypes fs

    getTVar env id = if fNew then useTVar env id
			     else lookupTVar env id

    -- lookup a type var. in the type env.... if it's not there, add it
    useTVar :: Env -> AST.Id -> TR (Env, Type)
    useTVar env id = case lookupTypeEnv (AST.idStr id) env of
	Just t  -> return (env, TVar t)
	Nothing -> do t <- newVarRef (AST.idStr id) (getSrcInfo id)
		      let tr   = (AST.idStr id, fromTVar t)
			  env' = extendTypeEnv env tr
		      return (env', t)

    -- simply look up the named type variable, fail if it's not there
    -- returns Env so that it can be used interchangably with useTVar
    lookupTVar :: Env -> AST.Id -> TR (Env, Type)
    lookupTVar env id = case lookupTypeEnv (AST.idStr id) env of
	Just t  -> return (env, TVar t)
	Nothing -> do
	    addErrorMsg id (errorMsg id ["Undefined type variable `" ++ 
					  AST.idOrigStr id ++ "'"])
	    return (env, bogusType)
	

consTypes :: (Bool, Bool) -> Env -> [AST.Type] -> TR (Env, [Res])
consTypes fs = procMany (consType fs)

-- builds a type constructor from an id
mkTCon :: AST.Id -> Type
mkTCon id = TCon (idToName id)

--------------------------------------------------------------------------------
-- internalise type schemes

consTSchm :: Env -> AST.TSchm -> TR (Env, Res)
consTSchm = consTSchmConf consTypeNew

consNewTSchm :: Env -> AST.TSchm -> TR (Env, Res)
consNewTSchm = consTSchmConf consTypeNewCons

consTSchmConf :: (Env -> AST.Type -> TR (Env, Res)) 
	      -> Env -> AST.TSchm -> TR (Env, Res)
consTSchmConf f env (AST.TSchm ctxt t) = do
    (env1, c) <- consCtxt env ctxt
    (env2, (t_t, c_t)) <- f env1 t
    return (env2, (t_t, c /\ c_t))

--------------------------------------------------------------------------------
-- generate internal constraints from AST constraints

consCnst :: Env -> AST.Cnst -> TR (Env, Constraint)
consCnst env (AST.Cnst ps) = do
    (env', cs) <- procMany consPrim env ps
    return (env', toConstraint cs)

consCtxt :: Env -> AST.Ctxt -> TR (Env, Constraint)
consCtxt env (AST.Ctxt ps) = do
    (env', ucs) <- procMany consPred env ps
    return (env', toConstraint ucs)

consPreds = procMany consPred 

consPred :: Env -> AST.Pred -> TR (Env, UCons)
consPred env (AST.Pred s id ts) = do
    (env',  psym) <- lookupPredId env id
    (env'', tcs) <- consTypesNew env' ts
    let (ts,_) = unzip tcs
        uc = njUC psym ts `withJust` s
    return (env'', uc)

-- lookup the given pred id in the penv.
-- FIXME: I'm not sure what constitutes a pred. declaration, so there's no
--	  environment initialisation, and we simply add any new predicates to
--	  the environment as they're used.
lookupPredId :: Env -> AST.Id -> TR (Env, Name)
lookupPredId env id = case lookupPredEnv (AST.idStr id) env of
    Just n  -> return (env, n)
    Nothing -> let str  = AST.idStr id
		   psym = mkName str (getSrcInfo id) str
		   env' = extendPredEnv env (str, psym)
	       in  return (env', psym)
    

-- NOTE: EqPrims representing desugared `True' constraints are justified by 
--	 `trueJust' (we never care about their source anyway)
--	 Make sure the `isTrueEqPrim' check below is consistent with the
--	 desugaring of True constraints in AST/ChParser/ParserMisc.hs 
consPrim :: Env -> AST.Prim -> TR (Env, Constraint)
consPrim env (AST.PredPrim p) = do 
    (env', uc) <- consPred env p
    return (env', toConstraint uc)

consPrim env eq@(AST.EqPrim _ t1 t2) = do 
    (env1, (t_t1, _c_t1)) <- consTypeNew env  t1
    (env2, (t_t2, _c_t2)) <- consTypeNew env1 t2
    let j = if isTrueEqPrim then trueJust
			    else locToJust (getSrcLoc eq)
	c3 = toConstraint ((t_t1 =+= t_t2) j)
    return (env2, c3)
  where
    isTrueEqPrim = case (t1, t2) of
	(AST.ConType t1', AST.ConType t2') 
	    | AST.idStr t1' == "intT1!" && AST.idStr t2' == "intT2!" -> True
	_ -> False


consPrims :: Env -> [AST.Prim] -> TR (Env, Constraint)
consPrims env aps = do
    (env', cs) <- procMany consPrim env aps
    return (env', andList cs)


--------------------------------------------------------------------------------
-- The interface

-- Generates all CHRs and goals for the Prog, using the standard initial 
-- environment. Takes a LocInfo in case we need to do any constraint matching 
-- for evidence generation purposes (as done by the implication solver.) 
-- Also takes a list mapping identifiers of variables (external to 
-- the module), to type-constraint pairs, a list of imported non-val.
-- declarations and a list of all recursive functions.
-- NOTE: We remove all methods from imported instance decs, before processing
-- them. (They may refer to out-of-scope identifiers, and we don't care about
-- re-checking them anyway.)
typeInference :: AST.Prog -> LocInfo -> [(IdStr, Res)] -> [AST.Dec] -> [SCC]
	      -> IO (SimpleResult ([InfResult],Matches))
typeInference p linfo vtcs impdecs0 progSCCs = do
    let tr = do (res, passed) <- inferenceTopLevel env p impdecs
		ms <- trGet matches
		return (res, ms, passed)
    res <- run (initState { sccs = progSCCs }) tr
    -- putStrLn ("vtcs: " ++ pretty vtcs)
    return $ case res of
	-- NOTE: errors are accumulated back-to-front
	Failure e b -> Failure (nub (reverse e)) b
	Success e ((res,ms,_),st) 
	    | anyCriticalErrors e -> simpleFailure (nub (reverse e))
	    | otherwise -> Success e (res,ms)
  where
    run st (TR f) = f st
    
    -- drop imported instance methods
    impdecs :: [AST.Dec]
    impdecs = map proc impdecs0
      where
	proc (AST.InstDec s (AST.Inst c p _)) = AST.InstDec s (AST.Inst c p [])
	proc d = d
    
    initState = St 0 [] [] [] linfo [] []

    (env,ext_chrs) = let vfs   = map mkVarRes vtcs
			 rules = map mkCHR vtcs
		     in  (stdEnv { varEnv = vfs ++ varEnv stdEnv }, rules)
      where
	mkVarRes x@(id,(t,c)) = Var id (mkSimpleTSchm t c)
	mkCHR x@(id,(t,c)) = let v  = TVar (mkVar "t")
				 eq = v =:= t
			     in  SimpRule HMRule [mkAnnUC (uc (id,(v,c)))] 
						   (eq /\ c)
	uc (id,(t,c)) = UC (mkFreeName id) [t] noJust

