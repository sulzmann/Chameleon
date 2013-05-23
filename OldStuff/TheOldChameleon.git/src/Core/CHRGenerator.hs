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
-- Constraint and CHR generation for the language defined in AST/Internal
-- 
-- NOTES: 
--  - We build LT while traversing the program, in genConsPat
--
-- TODO:
--  - we ought to allow annotated instance methods
--
-------------------------------------------------------------------------------

module Core.CHRGenerator (
    progCHRsGoals, InfGoal(..)
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

import AST.SrcInfo
import qualified AST.Internal as AST

import Config.CHRGenerator

--------------------------------------------------------------------------------
-- the TR (translation) monad

data State = St { num :: Int,			-- unique number store	
		  ltEnv :: LTEnv,		-- the LT parameter (so far)
		  parentStack :: ParentStack,	-- parents of current def
		  recursiveDefs :: [AST.Id],	-- list of recursive defs
		  config :: Options,		-- configuration options
		  goals  :: [InfGoal],		-- inference goals 
		  transUnknownTypeCons :: Bool}	-- a flag for the type trans
						--  (see: consType)

newtype TR a = TR (State -> IO (SimpleResult (a,State)))

-- (LT) types of all lambda vars
type LTEnv = [Type] 

-- stack of let vars from the immediate parent up
type ParentStack = [(Name, [Var])]	    

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
    initState = St 0 [] [] [] conf [] False
    conf = stdOptions

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

num' f st	  = st {num = f (num st)}
ltEnv' f st	  = st {ltEnv = f (ltEnv st)}
config'	f st	  = st {config  = f (config st)}
parentStack' f st = st {parentStack = f (parentStack st)}
goals' f st	  = st {goals = f (goals st)}
transUnknownTypeCons' f st = st {transUnknownTypeCons = 
				    f (transUnknownTypeCons)}

----------------------------------------
-- using the number store

getNum = trGet num
incNum = trUpdate $ num' (+1) 
setNum n = trUpdate $ num' (const n)

next = do n <- getNum
	  incNum
	  return n

----------------------------------------
-- using the LT env

getLT     = trGet ltEnv
addToLT x = trUpdate $ ltEnv' (x:)
clearLT   = trUpdate $ ltEnv' (const [])

----------------------------------------
-- using the parent stack

enterScope :: Name -> TR ()
enterScope nm = trUpdate $ parentStack' ((nm,[]):)

exitScope :: TR ()
exitScope = trUpdate $ parentStack' tail

enterScopeWithLocalVars :: Name -> [Var] -> TR ()
enterScopeWithLocalVars nm tvs = trUpdate $ parentStack' ((nm,tvs):)

parentName :: TR (Maybe Name)
parentName = do 
    ps <- trGet parentStack
    case ps of 
        [] -> return Nothing
        ((nm,_):_) -> return (Just nm)

parentLocalVars :: TR (Maybe [Var])
parentLocalVars = do 
    ps <- trGet parentStack
    case ps of
        [] -> return Nothing
        ((_,tvs):_) -> return (Just tvs)

atTopLevel :: TR Bool
atTopLevel = do 
    ps <- trGet parentStack 
    return (null ps) 

-- true if the named function is a parent
isAParent :: IdStr -> TR Bool
isAParent f = do
    ps <- trGet parentStack
    let ns = map (nameStr . fst) ps
    return (f `elem` ns)

-- returns a string which is a combination of the names of all of the
-- function's parents
parentsNameString :: TR IdStr
parentsNameString = do 
    ps <- trGet parentStack  
    let ns = reverse (map (nameStr . fst) ps)
        str = concat (intersperse ">" ns)
    return str 

-- given the name of a function currently in scope, generate a nested name, (a
-- combination of its identifier and the identifiers of its parents), which
-- will uniquely identify it
nestedName :: Name -> TR Name
nestedName nm = do 
    pn <- parentsNameString
    return $ if null pn then nm
			else nm { nameStr = (pn ++ ">" ++ nameStr nm) }


-- adds a goal to the state
addGoal :: InfGoal -> TR ()
addGoal ig = trUpdate $ goals' (ig:)

----------------------------------------
-- get a config. option

getConfigOpt :: (Options -> a) -> TR a
getConfigOpt f = do 
    conf <- trGet config
    return (f conf)

----------------------------------------
-- check if the given definition is recursive
-- (simply looks up the table in the TR state)

isRecursive :: AST.Id -> TR Bool
isRecursive nm = do 
    rec <- trGet recursiveDefs
    return (nm `elem` rec)


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

-- NOTE: we keep data constructors distinct from functions (let-bound things)
--	 since we need to keep track of any existential variables/constraints

data VarRes  = VarX { varXId :: IdStr,	-- lambda variable (Gamma)
		      varXType :: Type }
		      
	     | VarF { varFId :: IdStr,	    -- let variable    (E)
                      varFLoc :: Loc,	    -- location number
		      varFAnnot :: Bool,    -- is it annotated (universal) ?
		      varFRec :: Bool,	    -- is it recursive?
		      varFTop :: Bool,	    -- is it defined at the top-level?
                      varFGlobalTVars :: [Var], -- global tvars wrt this fun.
		      varFUCons :: UCons }  -- uc representing the type  

	     | DCon { dconId :: IdStr,		    -- data constructor
		      dconExistVars :: [Var],	    -- existential variables
		      dconConstraints :: Constraint,-- existential constraints
		      dconType :: Type,		    -- just type, no exist cons
		      dconUCons :: UCons }	    -- represents the whole type

instance Show VarRes where
    show (VarX id t) = "X " ++ id ++ ":" ++ show t
    show (VarF id _ _ _ _ _ u) = "F " ++ id ++ "|" -- ++ show u
    show (DCon id evs ecs t u) = "D " ++ id ++ "|" {- ++ show u ++ "," ++ show t ++
				 (" (exist, vs: " ++ show evs ++ 
				  "; cs: " ++ show ecs ++ ")") -}

varResId (VarX id _) = id
varResId (VarF id _ _ _ _ _ _) = id
varResId (DCon id _ _ _ _) = id

isVarX (VarX {}) = True
isVarX _ = False

isVarF (VarF {}) = True
isVarF _ = False


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

----------------------------------------

data TypeRes = TypeCon IdStr Type	-- internal type of a constructor (TCon)
	     | TypeVar IdStr Type	-- internal type of a variable    (TVar)
    deriving Show

typeResId (TypeCon id _) = id
typeResId (TypeVar id _) = id

typeResType (TypeCon _ t) = t
typeResType (TypeVar _ t) = t

isTypeVar (TypeVar {}) = True
isTypeVar _ = False

--------------------------------------------------------------------------------
-- Bogus results - use these as placeholders in case of an error 
-- (just so that we can continue, and hopefully accumulate more errors)

bogusIdStr :: IdStr
bogusIdStr = "Bogus, man!"

bogusType :: Type
bogusType = TVar (mkVar bogusIdStr)

bogusUCons :: UCons
bogusUCons = UC (mkFreeName bogusIdStr) [] noJust

bogusConstraint :: Constraint
bogusConstraint = trueConstraint

bogusRes :: Res
bogusRes = (bogusType, bogusConstraint)

bogusDCon :: VarRes 
bogusDCon = DCon bogusIdStr [] bogusConstraint bogusType bogusUCons

--------------------------------------------------------------------------------

type VarEnv = [VarRes]		    -- maps term variables to type/cons

type TypeEnv = [TypeRes]		-- maps type vars/contructors to Reps
type PredEnv = [(IdStr, Name)]		-- maps predicate symbols to Names

-- complete environment for constraint/CHR generation
data Env = Env { varEnv  :: VarEnv, 
		 typeEnv :: TypeEnv,
		 predEnv :: PredEnv }
    deriving Show


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
extendLTEnv   env x = ltEnv'   (x:) env
extendTypeEnv env x = typeEnv' (x:) env
extendPredEnv env x = predEnv' (x:) env
  

lookupPredEnv = lookupEnvGeneral predEnv
lookupEnvGeneral p id env = lookup id (p env)

lookupVarEnv :: IdStr -> Env -> Maybe VarRes
lookupVarEnv id env = let xs = filter ((==id) . varResId) (varEnv env)
		      in  listToMaybe xs

lookupTypeEnv :: IdStr -> Env -> Maybe TypeRes
lookupTypeEnv id env = let xs = filter ((==id) . typeResId) (typeEnv env)
		       in  listToMaybe xs

-- for external use
lookupVarEnvUCons :: IdStr -> Env -> Maybe UCons
lookupVarEnvUCons id env = do
    vf <- lookupVarEnv id env
    return (varFUCons vf)

----------------------------------------
-- standard environment

stdEnv = Env { varEnv  = [ -- miscVarF noSuchFieldStr,
			   -- miscVarF undefinedMethodStr,
			   -- miscVarF uninitialisedFieldStr,
			   -- miscVarF patternMatchFailedStr,
			   -- miscVarF bAndStr,
			   -- miscVarF bEqualsStr,
			   -- miscVarF bMapStr,
			   -- miscVarF bAppendStr,
			   -- miscVarF bSucc_IntStr,
			   -- miscVarF bLessThan_IntStr,
			   -- miscVarF bGreaterThan_IntStr,
			   -- miscVarF bEnumFromTo_IntStr,
			   -- miscVarF bEnumFromThenTo_IntStr,
			   miscDCon listStr listNullType,
			   miscDCon consStr listConsType,
			   miscDCon unitStr unitType,
			   miscDCon trueStr boolType,
			   miscDCon falseStr boolType ] ++ 
			   miscDCons [(tupleStr n,tupleConType n) | n<-[2..7]]++
			   miscDCons [(nListStr n,nListConType n) | n<-[1..7]],
			   
	       typeEnv = [ miscTypeCon arrowStr,	-- ->
			   miscTypeCon listStr,		-- []
			   miscTypeCon unitStr,		-- ()
			   miscTypeCon intStr,		-- Int
			   miscTypeCon integerStr,	-- Integer
			   miscTypeCon charStr,		-- Char
			   miscTypeCon floatStr,	-- Float
			   miscTypeCon doubleStr,	-- Double
			   miscTypeCon boolStr,		-- Bool
			   miscTypeCon "intT1!",
			   miscTypeCon "intT2!" ] ++ 
			   map (miscTypeCon . tupleStr) [2..7] ++ 
			   map (miscTypeCon . nListStr) [1..7],
			   
	       predEnv = [] }
  where
    miscTypeCon str = TypeCon str (TCon (mkFreeName str))
  
    miscVarX str = VarX str (TVar (mkVar str))

    miscVarF str = 
	let t = TVar (mkVar str)
	in  VarF str noLoc False False True [] (UC (mkFreeName str) [t] noJust)
	
    miscDCon str t = 
	let nm = mkFreeName str
	    uc = UC nm [TVar (mkVar str)] noJust
	in  DCon str [] trueConstraint t uc 

    miscDCons = map (uncurry miscDCon)


listNullType = let a = TVar (mkVar "a")
	       in  listType a 

listConsType = let a = TVar (mkVar "a")
	       in  listType a `arrow` a

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
-- generates variable vectors for lambda and scoped type variables

lambdaVarVec :: Env -> TR Type
lambdaVarVec env = do
    let ts = reverse [ t | (VarX _ t) <- varEnv env ]
    standardTypeList ts

lambdaVarVecClosed :: Env -> TR Type
lambdaVarVecClosed env = do
    let ts = reverse [ t | (VarX _ t) <- varEnv env ]
    closedTypeList ts

typeVarVec :: Env -> TR Type
typeVarVec env = do
    let ts = reverse [ t | (TypeVar _ t) <- typeEnv env ]
    standardTypeList ts

typeVarVecClosed :: Env -> TR Type                   
typeVarVecClosed env = do                            
    let ts = reverse [ t | (TypeVar _ t) <- typeEnv env ]
    closedTypeList ts           
                                

-- generates a scoped var. vec for only the given variables
-- this is used at call sites to pass through only variables which are global
-- to the function being called
limitedScopedVarVec :: [Var] -> TR Type
limitedScopedVarVec tvs = standardTypeList (map TVar tvs)


-- generates a vector containing only the variables present in the second
-- environment, but not in the first (the new/local variables)
localScopedVarVec :: Env -> Env -> TR Type
localScopedVarVec env0 env1 = 
    let te0 = filter isTypeVar (typeEnv env0)
	te1 = filter isTypeVar (typeEnv env1)
	l0  = length te0
	l1  = length te1
	ts  = reverse (map typeResType (take (l1 - l0) te1))
    in  closedTypeList ts
				    

ltVarVec :: TR Type
ltVarVec = getLT >>= standardTypeList . reverse

-- generates a standard type list, using vconsType for cons, and terminated by
-- a fresh variable
standardTypeList :: [Type] -> TR Type
standardTypeList ts = do
    nil <- newVar
    return (typeList vconsType nil ts)

closedTypeList :: [Type] -> TR Type
closedTypeList ts = return (typeList vconsType vnilType ts)

-- generates a type level list out of the given elements, 
-- using the supplied cons and nil type constructors
typeList :: Type -> Type -> [Type] -> Type
typeList cons nil vs  = foldr (\v t -> TApp (TApp cons v) t) nil vs

--------------------------------------------------------------------------------

-- Generates a user constraint which contains all of the variables in the
-- given constraints, except those only appearing within implications.
genVarsC0 :: Constraint -> UCons
genVarsC0 c = 
    let ucs = cUCons c
	bcs = cBCons c
	ts  = map TVar (nub (fv (ucs,bcs)))
	nm  = mkFreeName "C0Vars!"
	t = tupleType ts
    in  UC nm [t] noJust

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
    env0 <- initEnvTop env ds
    (env1, chrs_dat)   <- initDataDecs (env0 `addEnv` env) ds
    (env2, chrs_prim)  <- initPrimDecs env1 ds
    (env3, chrs_class) <- initClassDecs env2 ds
    (env4, chrs_inst)  <- initInstDecs env3 ds ds_imp
    (env5, chrs_rule)  <- initRuleDecs env4 ds
    return (env5, chrs_dat ++ chrs_rule ++ chrs_class ++ chrs_inst ++ chrs_prim)

----------------------------------------

-- process data declarations
initDataDecs :: Env -> [AST.Dec] -> TR (Env, [CHR])
initDataDecs env ds0 = do
    let ds = dataDecs ds0
    env0 <- initTypeCons (map dataType ds)
    let env1 = env0 `addEnv` env
    (env2, chrs) <- initDatCons env1 ds
    return (env2 `addEnv` env1, chrs)

  where
    -- filters out non-DataDecs
    dataDecs :: [AST.Dec] -> [AST.Dec]
    dataDecs = filter isDataDec

    isDataDec (AST.DataDec {}) = True
    isDataDec _ = False

    dataType (AST.DataDec _ dt _) = dt

-- Given a list of new data types, generate new type constructors and insert 
-- them into the environment (this must be done for all decls before data
-- constructors can be handled.)
initTypeCons :: [AST.DataType] -> TR Env
initTypeCons ds = do 
    envs <- mapM init ds
    return (sumEnvs envs)
  where 
    init (AST.DataType id _) = do 
	let str = AST.idStr id 
	    t   = TCon (mkFreeName str)
	    env = extendTypeEnv emptyEnv (TypeCon str t)
	return env
   

-- Takes current environment and a list of data declarations, and returns a new
-- environment with updated venv to include new data constructors.
initDatCons :: Env -> [AST.Dec] -> TR (Env, [CHR])
initDatCons env cs = do
    echrs <- mapM (initDatCon env) cs
    let (envs, chrs) = unzip echrs
    return (sumEnvs envs, concat chrs)

-- Add variables bound by the data dec. to the environment, and translate each
-- data constructor.
initDatCon :: Env -> AST.Dec -> TR (Env, [CHR])
initDatCon env (AST.DataDec _ (AST.DataType id ts) cs) = do 
    vs <- newVars (length ts)
    let trs  = zipWith TypeVar (map (AST.idStr . varTypeId) ts) vs
	con  = typeResType $ fromJust $ lookupTypeEnv (AST.idStr id) env
	t    = foldl TApp con vs
	env' = foldl extendTypeEnv env trs
    echrs <- mapM (initCon t env') cs
    let (envs, chrs) = unzip echrs
    return (sumEnvs envs, chrs)
  where
    varTypeId (AST.VarType id) = id
    varTypeId _ = bug "non-var type in new data type declaration"

initCon :: Type -> Env -> AST.Cons -> TR (Env, CHR)
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
	env''  = extendVarEnv emptyEnv (DCon str v_tvs c_ctxt t uc)
   
    return (env'', chr)


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
	        -- chr' = newCHRSrcPos pos chr
	    return (env3, chr)

    AST.PropRule ctxt cnst -> do
	    (env1, c1) <- consCtxt env ctxt
	    (env2, c2) <- consCnst env1 cnst
	    let info = ConsRule
	        chr  = PropRule info (cUCons c1) c2
	        -- chr' = newCHRSrcPos pos chr
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
    (env3, chrs_m) <- chrMethods env2 uc w
    let env4 = env3 `addEnv` env2 
	env5 = env4 { typeEnv = typeEnv env }	-- don't let out any type vars
    -- finally the F.D. rules
    chrs_fds <- mapM (initFunDep env2 is) (zip (repeat uc) fds)
    return (env5, chr_sub : chrs_m ++ concat chrs_fds)

chrMethods :: Env -> UCons -> [AST.Method] -> TR (Env, [CHR])
chrMethods env cuc ms = do
    echrs <- mapM chrMethod ms
    let (es,chrs) = unzip echrs
    return (sumEnvs es, chrs)
  where
    chrMethod :: AST.Method -> TR (Env, CHR)
    chrMethod (AST.Method id ts) = do
	(_env', (t_t, c_t)) <- consNewTSchm env ts
	-- generate the simplification rule
	t <- newVar
	let info = HMRule 
	    s   = getSrcInfo id
	    str = AST.idStr id
	    nm  = mkName str s str
	    uc  = njUC nm [t]
	    eq  = (t =:= t_t) `withJust` s
	    chr = SimpRule info [mkAnnUC uc] (cuc /\ eq /\ c_t)

	let env1 = emptyEnv {varEnv = [VarF str (getSrcLoc s) True False True [] uc]}
	    
	return (env1,chr)

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
	Just (TypeVar _ t) -> t
	_ -> bug ("FD variable `" ++ id ++ "' is unbound!" ++ 
		  "\nin env: " ++ show env)


----------------------------------------
-- process instance declarations

-- generates CHR rules from instance declarations 
initInstDecs :: Env -> [AST.Dec] -> [AST.Dec] -> TR (Env, [CHR])
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
initInsts :: Env -> [AST.Dec] -> [AST.Dec] -> TR (Env, [CHR])
initInsts env cs is = do 
    let cis = map getClass pis
    (env',chrss) <- procMany initInst env cis
    return (env', concat chrss)
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
initInst :: Env -> (AST.Dec, AST.Dec) -> TR (Env, [CHR])
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
    mchrs <- mapM (chrMethods env1 env3 c (ucc,uci)) dms
    -- puts ("mchrs:\n" ++ prettyLines mchrs)
	      
    return (env, [chr] ++ concat mchrs)
	    -- Why the heck did we want to pass the environment out?
	    -- (env3, [chr] ++ concat mchrs)

  where
    -- Generate CHRs from the given instance method dec., and a subsumption
    -- check against the method definition (from the class.)
    -- We also pass in the class and instance dec. class predicates.
    -- NOTE: cenv -- environment used to translate the class dec. pred
    --	      env -- environment used for the instance dec. (contains type
    --		     variables from the instance Pred.)
    chrMethods :: Env -> Env -> Constraint -> (UCons,UCons) -> 
		  (AST.Dec, AST.Method) -> TR [CHR]
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

	addGoal (SubGoal id (map fromTVar tlv) (toConstraint sub))

{-
	puts ("c_ctxt: " ++ pretty c_ctxt)
	puts ("t_m: " ++ pretty t_m)
	puts ("c_m: " ++ pretty c_m)
	puts ("uc1 : " ++ pretty uc1)
	puts ("uc2 : " ++ pretty uc2)
	puts ("c_ts: " ++ pretty c_ts)
	puts ("goal: " ++ pretty goal)
-}
	return chrs
  
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


    lookupUC env id = case lookupVarEnv id env of
	Just (VarF _ _ ann rec _ _ uc) -> let j | ann || not rec = adminJust
						| otherwise = monoAdminJust
					  in  uc `appendJust` j
	_ -> bug ("consLetBnd - user constraint: `" ++ id ++ "' not found")

----------------------------------------
-- process primitive declarations

initPrimDecs :: Env -> [AST.Dec] -> TR (Env, [CHR])
initPrimDecs env ds0 = do
    let ds = filter isPrimDec ds0
    chrrs <- sequence [ init (getSrcInfo s) p | AST.PrimDec s p <- ds ] 
    let (chrs,rs) = unzip chrrs
	env' = foldl extendVarEnv env rs
    return (env', chrs)
  where
    init info (AST.Prim id _ ts) = do
	let l = getSrcLoc info
	t1 <- newVarLoc l
	(_,(t2,c)) <- consNewTSchm env ts
	let str  = AST.idStr id
	    psym = mkName str (getSrcInfo id) str
	    uc   = njUC psym [t1]
	    r    = VarF str l False False True [] uc
	    
	    info = HMRule
	    rhs  = t1 =:= t2 /\ c 
	    chr  = SimpRule info [uc] rhs
	
	return (chr, r)
  
    isPrimDec (AST.PrimDec {}) = True
    isPrimDec _ = False


--------------------------------------------------------------------------------
-- environment initialisation for values

-- call for top-level values
initEnvTop :: Env -> [AST.Dec] -> TR Env
initEnvTop = initEnvConf True

-- call for nested values
initEnv :: Env -> [AST.Dec] -> TR Env
initEnv = initEnvConf False


-- Initialise the environment with entries for value declarations.
-- Also takes a flag which indicates whether these decs are at the top level.
-- NOTE: In order to keep predicate names consistent between constraint and CHR
-- generation, we use the location number of the declaration as the name id
-- number. This is safe, since all fresh numbers are greater than any of the
-- location numbers assigned by the parser (because we use the same store.)
-- NOTE: entries for overloaded declarations are already added by initTopEnv
initEnvConf :: Bool -> Env -> [AST.Dec] -> TR Env
initEnvConf top env ads = do 
    envs <- mapM init ads
    return (sumEnvs envs)
  where
    init d = case d of 
	AST.ValDec _ (AST.LetBnd s id e)       -> initLB False (s, id, e)
	AST.ValDec _ (AST.LetBndAnn s id AST.Exist _ e)-> initLB False (s,id ,e)
	AST.ValDec _ (AST.LetBndAnn s id AST.Univ _ e) -> initLB True (s, id ,e)
	_ -> return emptyEnv
      where
	initLB ann (s, id, e) = do
	    t <- newVar
	    l <- newVar
	    v <- newVar
	    rec <- isRecursive id
	    let str = AST.idStr id
		nm  = mkIdName top id
		uc  = njUC nm [t,l,v]
		r   = VarF str (getSrcLoc s) ann rec top gtvs uc
	    return (extendVarEnv emptyEnv r)

    gtvs = let tenv = typeEnv env
           in  reverse [ fromTVar t | (TypeVar _ t) <- tenv, isTVar t ]

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
-- CHR generation

-- First initialise the environment with all non-value declarations
-- i.e. data, rules, overloads (stuff that only occurs at the top level).
-- The list of declarations contains only those which are imported.
-- Then translate the values.
chrProg :: Env -> AST.Prog -> [AST.Dec] -> TR (Env, [CHR])
chrProg env (AST.Prog ms) ds_imp = do
    let ds = concatMap AST.moduleDecs ms
    (env1, chrs_init) <- initTopEnv env ds ds_imp
    (env2, chrs_val)  <- chrTopDecs env1 ds
    let chrs_all = (chrs_init ++ chrs_val)
    return (env2, chrs_all)

-- as below, but these are top-level declarations, so clear LT between calls
chrTopDecs :: Env -> [AST.Dec] -> TR (Env, [CHR])
chrTopDecs env ads = do
    env0 <- initEnvTop env ads
    let env1 = env0 `addEnv` env
    chrss <- mapM (\d -> do clearLT
			    chrDec env1 True d) ads
    return (env1, concat chrss)
   

-- generates CHRs from a list of declarations all at the same scope
chrDecs :: Env -> [AST.Dec] -> TR [CHR]
chrDecs env ds = do
    -- initialise the environment, by adding entries for 
    -- all the declarations at this scope
    env0 <- initEnv env ds
    let env1 = env0 `addEnv` env
    chrss <- mapM (chrDec env1 False) ds
    return (concat chrss)


-- Flag indicates whether the binding is at the top-level.
-- If we're at the top, then also generate the inference goal (via consLetBnd.)
chrDec :: Env -> Bool -> AST.Dec -> TR [CHR]
chrDec env top d = case d of
    AST.ValDec s lb -> do consLetBnd env top lb
			  chrLetBnd  env top lb 

    -- other cases are handled elsewhere 
    -- (probably during top-level initialisation)
    _		    -> return []


-- flag indicates whether the binding is at the top-level
chrLetBnd :: Env -> Bool -> AST.LetBnd -> TR [CHR]
chrLetBnd env top lb = case lb of

    -- unannotated let binding
    AST.LetBnd s id e -> do
	let idstr = AST.idStr id
	    nm	  = mkIdName top id

	-- this definition is now the parent
	enterScope nm
	-- generate constraints and CHRs from the expression
	(t_e, c_e) <- consExp env e
	chrs_e     <- chrExp env e
	exitScope
	lvec <- lambdaVarVec env
	vvec <- typeVarVec env
	-- generate the simplification rule
	[t,l,v] <- newVars 3
	let info = HMRule
	    uc   = njUC nm [t,l,v]
	    eqs  = (t =+= t_e) s /\ l =:= lvec /\ v =:= vvec
	    rhs  = eqs /\ c_e
	    rhs' = genVarsC0 rhs /\ rhs
	    chr  = SimpRule info [uc] rhs'

	return (chr:chrs_e)

    -- annotated let binding
    AST.LetBndAnn s id at ts e -> do
	let nm   = mkIdName top id
	    nm_a = nm { nameStr = mkAnnIdStr (nameStr nm) } -- annotated (f_a)

	-- process the annotation first, since it scopes over the entire RHS
	(env', (t_t, c_t)) <- consNewTSchm env ts

	-- this definition is now the parent (refer to it via the annotation)
	enterScope nm_a
	-- generate constraints and CHRs from the expression
	(t_e, c_e) <- consExp env' e
	chrs_e     <- chrExp env' e
	exitScope
	lvec <- lambdaVarVec env
	-- In the case of a ::: annotation, the variable list at the definition
	-- site should not include the fresh variables. (This is the same as
	-- the case of the annotation CHR of a :: declaration.)
	vvec <- typeVarVec (if at == AST.Exist then env else env')
	-- generate the inference simplification rule
	[t,l,v] <- newVars 3
	let info = HMRule
	    uc   = njUC nm [t,l,v]
	    eqs  = (t =+= t_e) s /\ l =:= lvec /\ v =:= vvec
	    rhs  = eqs /\ c_e
	    rhs' = genVarsC0 rhs /\ rhs
	    chr  = SimpRule info [uc] rhs'

	-- If its a universal annotation, we still need to generate the
	-- appropriate annotation CHR. If its only an exist. annotation, just
	-- add the declared type and constraints to the inference CHR.
	case at of
	  AST.Exist -> let chr' = addToCHRBody chr (t =:= t_t /\ c_t)
		       in  return (chr':chrs_e)

	  AST.Univ -> do 
	    -- generate the annotation CHR
	    vvec    <- typeVarVec env
	    [t,l,v] <- newVars 3
	    let info  = HMRule
		uc_a  = njUC nm_a [t,l,v]
		eq    = (t =+= t_t) s /\ v =:= vvec
		chr_a = SimpRule info [uc_a] (eq /\ c_t)
	    return (chr_a:chr:chrs_e)


----------------------------------------
-- generate CHRs from expression

chrExp :: Env -> AST.Exp -> TR [CHR]
chrExp env exp = case exp of
    AST.VarExp  id -> return []
    AST.ConExp  id -> return []  
    AST.LitExp  l  -> return []
    
    AST.AppExp  s e1 e2 -> do chrs1 <- chrExp env e1 
			      chrs2 <- chrExp env e2 
			      return (chrs1 ++ chrs2)
        		  
    AST.AbsExp  s id e  -> do (env', _) <- consPat env (AST.VarPat id)
			      chrExp env' e
    
    AST.LetExp  s lbs e -> do new <- let ds = map (AST.ValDec s) lbs
        			     in  initEnv env ds
			      let env' = new `addEnv` env
			      chrs_lb <- mapM (chrLetBnd env' False) lbs
			      chrs_e  <- chrExp env' e
			      return (concat (chrs_e : chrs_lb))
        		  
    AST.CaseExp s es ms -> do chrs_e <- mapM (chrExp env) es
			      chrs_m <- mapM (chrMatch env) ms
			      return (concat (chrs_e ++ chrs_m))

chrMatch :: Env -> AST.Match -> TR [CHR]
chrMatch env m@(AST.Match ps e) = do
    (env', _) <- consPatsAccum env ps
    chrExp env' e

--------------------------------------------------------------------------------
-- Constraint generation


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
-- Translating let bindings:
--  - generates the inference goals / subsumption constraints
--  - also, returns the gratuitous up-call to the binding  (not implemented yet)
--    (just in case it's not called anywhere else)
-- Flag indicates whether we're at the top level.
consLetBnd :: Env -> Bool -> AST.LetBnd -> TR Constraint
consLetBnd env top lb = case lb of

    -- NOTE: A let-binding in Chameleon is just a binding, there's no "body".
    --       (for that we have let expressions.)
    AST.LetBnd s id e -> do
	let uc = lookupUC id
	addGoal (InfGoal id top (map fromTVar (ucTypes uc))
				(toConstraint (uc `withJustOf` s)))
	return trueConstraint

    -- There's no subsumption check, this is the same as the unannotated case.
    AST.LetBndAnn s id AST.Exist ts e -> let lb' = AST.LetBnd s id e
					 in  consLetBnd env top lb'

    -- We add a subsumption goal, and an inference goal (which just calls the
    -- annotation CHR.) This is okay, since we only care about the types of
    -- top-level things here (so there's no annotation context to consider.)
    AST.LetBndAnn s id AST.Univ ts e -> do
	let uc = lookupUC id
	(env', (t_ts, c_ts)) <- consNewTSchm env ts
	let tlv@[t,l,v] = ucTypes uc

	-- add the inference goal
	addGoal (InfGoal id top (map fromTVar tlv) (toConstraint (mkAnnUC uc)))

	-- generate the subsumption goal
	lvec <- lambdaVarVecClosed env
	vvec <- typeVarVecClosed env'
	-- only quantify over the local type variables (remove globals)
	let vs  = let v = [ fromTVar t | TypeVar _ t <- typeEnv env ] 
		  in  nub (fv (t_ts,c_ts) `without` v)
	    lhs = t =:= t_ts /\ l =:= lvec /\ v =:= vvec /\ c_ts
	    sub = IC vs (cUCons lhs, cBCons lhs) ([uc],[],[]) noJust
	-- if we're at the top level, add the subsumption goal
	when top (addGoal (SubGoal id (map fromTVar tlv) (toConstraint sub)))

	return (toConstraint sub)

  where
    lookupUC id = case lookupVarEnv (AST.idStr id) env of
	Just (VarF _ _ ann rec _ _ uc) -> let j | ann || not rec = adminJust
						| otherwise = monoAdminJust
					  in  uc `appendJust` j
	_ -> bug "consLetBnd - user constraint not found"

----------------------------------------
-- translating expressions

consExps :: Env -> [AST.Exp] -> TR [Res]
consExps env es = do (_, rs) <- procMany gen env es
		     return rs
  where
    gen env e = do r <- consExp env e
		   return (env, r)

-- Generates types/constraints out of expressions.
-- Some typing rules, and their implementation (obviously) can be found below.
consExp :: Env -> AST.Exp -> TR Res
consExp env exp = case exp of
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
	let mv = lookupVarEnv (AST.idStr id) env
	if isNothing mv then -- record the error, and return a bogus type
			     do errVarUndefined id	
				return bogusRes
			else trans (fromJust mv)
      where
	trans vr = case vr of
	    -- We generate the same constraints for a data constructor as for 
	    -- an unannotated let-bound variable at the top level.
	    DCon id _ _ _ uc -> trans (VarF id noLoc False False True [] uc)
	
	    VarX _ t0 -> do
		-- Justify the eq. constraint by both the expression and 
		-- binding location, so that the binding location is part of 
		-- any type error report. NOTE: we always put the location of 
		-- use before the binding location, so that we can always find 
		-- the definition that the constraint arose from by examining 
		-- only the leading location number.
		t <- newVarLoc l
		let c = (t =+= t0) j -- `appendJustOf` t0
		return (t, toConstraint c)

	    VarF id loc a rec top gtvs uc0 -> case ucTypes uc0 of
		[_t,_l,_v] -> do
		    t   <- newVarLoc l
		    par <- isAParent id
		    -- if id is a parent, then generate the lambda vector
		    -- otherwise, leave it blank 
		    -- FIXME: also generate the vector for calls to children
		    l <- if top then newVar else lambdaVarVecClosed env
		    v <- if top then newVar else typeVarVecClosed env
		    let uc = uc0 { ucTypes = [t,l,v] } `withJust` j
		    return (t, toConstraint $ if a then mkAnnUC uc
						   else uc)

		[_t] -> do t <- newVarLoc l
			   let uc = uc0 { ucTypes = [t] } `withJust` j
			   return (t, toConstraint $ if a then mkAnnUC uc
							  else uc)

                _    -> errMalformedUCons uc0

    -- we translate constructors as functions
    AST.ConExp id -> do
	let mv = lookupVarEnv (AST.idStr id) env
	if isNothing mv then do errConUndefined id
				return bogusRes
	  else do
	    t' <- newVarLoc l
	    let fromUC uc = case ucTypes uc of
		    [_t] -> let uc' = reJust j $ uc { ucTypes = [t'] }
			    in  return (t', toConstraint uc')
		    _    -> errMalformedUCons uc
	    case fromJust mv of
		VarF _ _ _ _ _ _ uc -> fromUC uc
		DCon _ _ _ _ uc   -> fromUC uc
		r -> bug ("ConExp missing case: " ++ show r)


    {-----------------------------------------------------------

	i |- (t1,c1)	t fresh
     ---------------------------------
	env, e |- (t, t = t1 /\ c1)

    -----------------------------------------------------------}
    AST.LitExp i -> do
	(t, c) <- consLit i
	t' <- newVarLoc l
	-- return (t', reJust j (t' =:= t /\ c)) 
	return (t', (t' =+= t) j /\ c)


    {-----------------------------------------------------------

	env, e1 |- (t1,c1)
	env, e2 |- (t2,c2)
	c3 = (t1 = t2 -> t'_l)_l
	c4 = (t_l = t'_l)_l	    t_l, t'_l fresh
     --------------------------------------------------
	env, (e1 e2)_l |- (t_l, c3 /\ c4 /\ c1 /\ c2)

    -----------------------------------------------------------}
    AST.AppExp _ e1 e2 -> do
	(t1, c1) <- consExp env e1 
	(t2, c2) <- consExp env e2 
	t3  <- newVarLoc l
	t3' <- newVarLoc l
	let c3 = (t1 =+= t2 `arrow` t3') j
	    c4 = (t3 =+= t3') j
	return (t3, c3 /\ c4 /\ c1 /\ c2)


    {-----------------------------------------------------------

	env, id |-_p (env', t1, c1)	-- extend env
	env', e |- (t2, c2)		
	c = (t_l = t1 -> t2)_l /\ c1 /\ c2    t_l fresh
     ------------------------------------------------------
	env, (\id -> e)_l |- (t_l, c)

    -----------------------------------------------------------}
    AST.AbsExp _ id e -> do 
	-- NOTE: the pattern is a single variable -- it won't have any
	--	 context constraints, or exist. vars etc.
	(env', (t1, c1, _, _)) <- consPat env (AST.VarPat id)
	(t2 , c2)  <- consExp env' e
	t <- newVarLoc l
	let c = (t =+= t1 `arrow` t2) j /\ c1 /\ c2
        return (t, c)

    -- NOTE: remember that we allow matching over multiple expressions
    AST.CaseExp _ e ms -> do
	r_e <- consExps env e
	let (t_es, c_es) = unzip r_e
	r_ms <- consMatches env ms
	t <- newVarLoc l
	let (t_ms, c_ms) = unzip r_ms
	    ft  = foldr arrow t t_es
	    eqs = listEq j ft t_ms
	return (t, c_es /\ eqs /\ c_ms)
	

    {-----------------------------------------------------------

	env,  lbs |-_init env'	    -- initialise env.
	env', lbs |- (_, c_lbs)
	env', e |- (t_e, c_e)
	c = (t_l = t_e)_l /\ c_lbs /\ c_e   t_l fresh
     --------------------------------------------------
	env, (let bnds in e)_l |- (t_l, c)

    -----------------------------------------------------------}
    AST.LetExp s lbs e -> do 
	new <- -- convert the bindings to declarations to init. the environment
	       let ds = map (AST.ValDec s) lbs
	       in  initEnv env ds
	let env' = new `addEnv` env
	c_lbs <- mapM (consLetBnd env' False) lbs
        (t_e, c_e) <- consExp env' e
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

consMatches :: Env -> [AST.Match] -> TR [Res]
consMatches env = mapM (consMatch env)

-- returns the type of match as a function type, 
-- ie. t_pat1 -> ... -> t_patn -> t_res
--
-- ERROR REPORTING NOTE: We want the polymorphic variables in the implication to
-- refer to their pattern binding locations.
consMatch :: Env -> AST.Match -> TR Res
consMatch env m@(AST.Match ps e) = do
    (env', (rs, evs, ec)) <- consPatsAccum env ps
    -- puts ("evs: " ++ show evs)
    let (t_ps, c_ps) = unzip rs
    (t_e, c_e) <- consExp env' e


    t <- newVar
    let c_match = t =:= foldr arrow t_e t_ps
	c_rhs =  c_ps /\ c_e
        -- if there are no exist. variables and no context constraints, then 
        -- don't generate an implicatation
	c' | null evs && ec == trueConstraint = c_match /\ c_rhs
	   | otherwise = let left  = (cUCons ec, cBCons ec)
			     right = (cUCons c_rhs, cBCons c_rhs, cICons c_rhs)
                             ic    = IC evs left right noJust
                         in  ic /\ c_match 
    return (t, c')

{-
    t <- newVar
    let c = t =:= (foldr arrow t_e t_ps) /\ c_ps
        -- if there are no exist. variables and no context constraints, then 
        -- don't generate an implicatation
	c' | null evs && ec == trueConstraint = c /\ c_e
	   | otherwise = let left  = (cUCons ec, cBCons ec)
			     right = (cUCons c_e, cBCons c_e, cICons c_e)
                             ic    = IC evs left right noJust
                         in  ic /\ c
    return (t, c')
-}
-- NOTE: we used to do the following transformation in order to avoid having
-- any nested implications.
{-
	    -- lift out any nested implications in the RHS.
	    -- i.e. A ->^a (B /\ (C ->^b D))
	    -- becomes: A ->^a B  and  A /\ C ->^a+b D
           | otherwise  = let ics  = cICons c_e
			      left = (cUCons ec, cBCons ec)
			      ic   = IC evs left 
					(cUCons c_e, cBCons c_e, []) noJust
			      ics' = map (liftIC left evs) ics
			  in  ic /\ ics' /\ c
	      where
		liftIC :: ([UCons],[BCons]) -> [Var] -> ICons -> ICons
		liftIC (ucs0,bcs0) vs' (IC vs (ucs,bcs) r j) = 
			IC (vs'++vs) (ucs++ucs0,bcs++bcs0) r j
{-
    puts ("c_e: \n" ++ pretty (cUCons c_e) ++ " " ++ pretty (cBCons c_e))
    puts ("c: " ++ pretty c)
    puts ("implications:\n" ++ unlines (map pretty (cICons c_e)))
-}  

--  return (t, c')
-}

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
consPat env pat = case pat of

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
	    tl  <- newVarLoc l
	    addToLT tl
	    let env' = extendVarEnv env (VarX (AST.idStr id) tx)
	    return $ if AST.idStr id == "_"
	      then (env,  (tl, trueConstraint, [], trueConstraint))
	      else let c = toConstraint ((tl =+= tx) l)
		   in  (env', (tl, c, [], trueConstraint))

    AST.LitPat lt -> do 
	    (t_l, c_l) <- consLit lt
	    t <- newVarLoc l
	    let c = reJust j (t =:= t_l /\ c_l)
	    return (env, (t, c, [], trueConstraint))

    -- 1. look up the constructor
    -- 2. if there are any existential variables, don't call the 
    --    constructor simp. rule to get the constructor's type, since that
    --    will drag in the exist. constraints, instead just get its type
    --    directly from the environment
    --    (if there are no exist. vars., just call the user constraint)
    AST.ConPat s id aps -> do
	    -- we need to rename these types/constraints
	    dc@(DCon id evs1' ec1' t' uc') <- getDC 
	    (evs1, ec1, t, uc) <- rename (evs1',ec1',t',uc' `withJustOf` s)
	    eps@(env', (rs, evs2, ec2)) <- consPatsAccum env aps
	    let (t_ps, c_ps) = unzip rs
	    t_res <- newVarLoc l
	    t_uc  <- newVar
	    let t_con = foldr arrow t_res t_ps
		
	    -- if there are no exist. vars and no context constraints, call the 
	    -- ucons to get the type of the constructor, else just use the type
	    -- in the environment (to avoid pulling in exist cons) 
	    -- i.e. we avoid building an implication if it's just going to have 
	    -- True on the lhs, and assume the solved form will just be the 
	    -- rhs, so we go straight to those constraints here.
		c_con | null evs1 && ec1 == trueConstraint = 
				      let uc' = uc { ucTypes = [t_uc] }
				      in  uc' /\ t_uc =:= t_con
			-- need to rename the universal variables
		      | otherwise = toConstraint (t_con =:= t)

	    let ec3  = (ec1 `prependJustOf` s) /\ ec2
		evs3 = evs1 ++ evs2
		c    = c_con /\ c_ps
	    return (env', (t_res, c, evs3, ec3))

      where
	str   = AST.idStr id
	
	envConsIds = [ id | (DCon id _ _ _ _) <- varEnv env ]
	
	getDC = do
	    let mv = lookupVarEnv str env
	    if isNothing mv
	      then do addErrorMsg s (errorMsg s
			    ["Undefined data constructor `" ++ str ++ "'",
			     alternatives str envConsIds ])
		      return bogusDCon
		    
	      else case fromJust mv of
		dc@(DCon {}) -> return dc
		x -> bug ("constructor in env, but it's not a DCons! " ++ 
			  show x)

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
	    t  <- do u <- trGet transUnknownTypeCons   
		     if u then return (TCon (mkFreeName (AST.idStr id)))
			  else lookupTCon env id
	    let c_eq = toConstraint ((t' =+= t) j)
	    return $ if fCons then (env, (t', c_eq))
			      else (env, (t, trueConstraint))	


    -- Handle function arrow as a special case.
    -- (Never abstract it away into a constraint, as per ConTyps.)
    AST.AppType _ (AST.AppType _ (AST.ConType id) t1) t2 
	| AST.idStr id == "->" -> do
	    t' <- newVarLoc l
	    (env1, (t1', c1)) <- consType' env  t1
	    (env2, (t2', c2)) <- consType' env1 t2
	    t_arr <- lookupTCon env id
	    let t    = TApp (TApp t_arr t1') t2'
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
	Just (TypeVar _ t) -> return (env, t)
	Nothing -> do t <- newVarRef (AST.idStr id) (getSrcInfo id)
		      let tr   = TypeVar (AST.idStr id) t
			  env' = extendTypeEnv env tr
		      return (env', t)

    -- simply look up the named type variable, fail if it's not there
    -- returns Env so that it can be used interchangably with useTVar
    lookupTVar :: Env -> AST.Id -> TR (Env, Type)
    lookupTVar env id = case lookupTypeEnv (AST.idStr id) env of
	Just (TypeVar _ t) -> return (env, t)
	Nothing -> do
	    addErrorMsg id (errorMsg id ["Undefined type variable `" ++ 
					  AST.idOrigStr id ++ "'"])
	    return (env, bogusType)
	
    -- lookup a type constructor in the type env.
    lookupTCon :: Env -> AST.Id -> TR Type
    lookupTCon env id = case lookupTypeEnv (AST.idStr id) env of
	Just (TypeCon _ t) -> return t
	Nothing	-> do
	    addErrorMsg id (errorMsg id ["Undefined type constructor `" ++ 
					 AST.idOrigStr id ++ "'",
					 alternatives (AST.idStr id) envIds ])
	    return bogusType
      where
	envIds = [ id | (TypeCon id _) <- typeEnv env ]
	    

consTypes :: (Bool, Bool) -> Env -> [AST.Type] -> TR (Env, [Res])
consTypes fs = procMany (consType fs)

--------------------------------------------------------------------------------
-- internalise type schemes

consTSchm :: Env -> AST.TSchm -> TR (Env, Res)
consTSchm = consTSchmConf consTypeCurCons

consNewTSchm :: Env -> AST.TSchm -> TR (Env, Res)
consNewTSchm = consTSchmConf consTypeNewCons

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
-- environment. Also takes a list mapping identifiers of variables (external to 
-- the module), to type-constraint pairs, a list of imported non-val.
-- declarations and a list of all recursive functions.
-- NOTE: We remove all methods from imported instance decs, before processing
-- them. (They may refer to out-of-scope identifiers, and we don't care about
-- re-checking them anyway.)
progCHRsGoals :: AST.Prog -> [(IdStr, Res)] -> [AST.Dec] -> [AST.Id] 
	      -> IO (SimpleResult ([CHR],[InfGoal]))
progCHRsGoals p vtcs impdecs0 recs = do
    let tr = do -- NOTE: Initially `transUnknownTypeCons' is set to True when
		-- translating all of the imported, external type and class
		-- declarations. This is necessary because those declarations
		-- may refer to types which are not imported into this module.
		-- e.g. A imports B, B imports C
		--	C contains: data T = S
		--	B contains: data R = R T
		--	A contains: r = R
		-- To process A we literally include B's data declaration.
		-- However, we don't include the declaration from C (which is
		-- not visible to A), which means we can't translate B's data
		-- declaration in A. Setting the flag gets around this by 
		-- telling the type generator to blindly accept any undefined
		-- type constructors. This is safe, since we'd have already
		-- successfully processed C and B anyway.
		(env1, chrs_init) <- initTopEnv env impdecs []
		trSet transUnknownTypeCons' False
		(env2, chrs_rest) <- chrProg env1 p impdecs
		return (env2, chrs_init ++ chrs_rest)
    res <- run (initState { recursiveDefs = recs }) tr
    return $ case res of
	-- NOTE: errors are accumulated back-to-front
	Failure e b -> Failure (nub (reverse e)) b
	Success e ((_,chrs),st) 
	    | anyCriticalErrors e -> simpleFailure (nub (reverse e))
	    | otherwise -> Success e (chrs ++ ext_chrs, reverse (goals st))
  where
    run st (TR f) = f st
    
    -- drop imported instance methods
    impdecs :: [AST.Dec]
    impdecs = map proc impdecs0
      where
	proc (AST.InstDec s (AST.Inst c p _)) = AST.InstDec s (AST.Inst c p [])
	proc d = d
    
    initState = St 0 [] [] [] stdOptions [] True

    (env,ext_chrs) = let vfs   = map mkVarF vtcs
			 rules = map mkCHR  vtcs
		     in  (stdEnv { varEnv = vfs ++ varEnv stdEnv }, rules)
      where
	mkVarF x@(id,(t,c)) = VarF id noLoc True False True [] (uc x)
	mkCHR  x@(id,(t,c)) = let v  = TVar (mkVar "t")
				  eq = v =:= t
			      in  SimpRule HMRule [mkAnnUC (uc (id,(v,c)))] 
						   (eq /\ c)
	uc (id,(t,c)) = UC (mkFreeName id) [t] noJust

