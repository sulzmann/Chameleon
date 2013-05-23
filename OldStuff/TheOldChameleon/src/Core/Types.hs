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
-- Types.
--
--------------------------------------------------------------------------------

module Core.Types (
    Var, mkVar, mkRefVar, mkLocVar,
    varName, varLoc, isTVar, isTCon, isTApp,
    isTuple, isList, typeTCons,

    fromTVar, fromTCon,
    varNameStr,
    Type(..),

    TypeOps, apply, fv, rename, Subst, idSubst, buildSubst,
    renameSubst, composeSubst, prettyRename, prettyRenameUpper,
    prettyRenameExplicitFV
)
where

import Char
import List
import Maybe
import Monad
-- import Data.FiniteMap
import Data.Map
import Debug.Trace

import Misc
import Core.Name
import Core.Justify
import AST.SrcInfo


--------------------------------------------------------------------------------
-- Type language

-- WARNING: It is *critical* that for Var that: \x -> read (show x) == x
--          We depend on this law in the implication solver. It *will* crash if
--          this is not the case!
data Var = Var { varName :: Name }
    deriving (Eq, Ord, Show, Read)

data Type = TVar Var 
	  | TCon Name
	  | TApp Type Type 
    deriving (Eq, Show)

-- creates a new Var (with no source information)
mkVar :: String -> Var
mkVar id = Var (mkFreeName id)

varNameStr :: Var -> String
varNameStr = nameStr . varName

-- creates a new Var with a location number reference
mkLocVar :: String -> Loc -> Var
mkLocVar str l = Var (mkLocName str l)

-- builds a variable with source information, takes: the original source name, 
-- source information, and the variable's name
-- (a variable with a `reference' to its origin)
mkRefVar :: String -> SrcInfo -> String -> Var
mkRefVar orig s str = Var (mkName orig s str)

fromTVar :: Type -> Var
fromTVar (TVar n) = n
fromTVar _ = bug "fromTVar: not a TVar!"

fromTCon :: Type -> Name
fromTCon (TCon n) = n
fromTCon _ = bug "fromTCon: not a TCon!"

isTVar, isTCon, isTApp :: Type -> Bool
isTVar (TVar {}) = True
isTVar _ = False

isTCon (TCon {}) = True
isTCon _ = False

isTApp (TApp {}) = True
isTApp _ = False

varLoc :: Var -> Loc
varLoc (Var n) = nameLoc n

tvarLoc :: Type -> Loc
tvarLoc = varLoc . fromTVar

-- NOTE: This only makes sense for extracting a `justification' from a
--	 variable! (Only used to support justification sugar.) 
instance Justified Type where
    getJust = getJust . tvarLoc


instance Pretty Var where
    pretty (Var n) = pretty n

instance Pretty Type where
    -- prec 0: infix
    -- prec 1: application
    -- prec 2: atomic
    prettysPrec n (TVar tv) ss = pretty tv ++ ss
    prettysPrec n (TCon tc) ss 
	| nameStr tc == "<>" = "<>"	-- type-level nil
	| otherwise	     = infixParens (pretty tc) ++ ss
    prettysPrec n t@(TApp t1 t2) ss =
	let no_con =
	     if n > 1
		then '(' : prettysPrec 1 t1 (" " ++ prettysPrec 2 t2 (')' : ss))
		else prettysPrec 1 t1 (" " ++ prettysPrec 2 t2 ss)

	    non_lst =  let mts = tupleTypes t 
			   ts  = fromJust mts
		       in  if isNothing mts
			      then no_con
			      else '(': commas (List.map pretty ts) ++ ")" ++ ss
	in case t1 of
	    TApp (TCon (Name _ "->")) t1
		| n > 0 -> '(' : prettysPrec 1 t1 ("->" ++ prettysPrec 0 t2 (')' : ss))
		| otherwise -> prettysPrec 1 t1 ("->" ++ prettysPrec 0 t2 ss)
	
	    -- type-level list (cons)
	    TApp (TCon (Name _ ";")) t1
		| n > 0 -> '(' : prettysPrec 1 t1 (";" ++ prettysPrec 0 t2 (')' : ss))
		| otherwise -> prettysPrec 1 t1 (";" ++ prettysPrec 0 t2 ss)
	
	    TCon (Name _ "[]") -> "[" ++ pretty t2 ++ "]" ++ ss

	    t1 -> non_lst

--------------------------------------------------------------------------------

-- class of basic operations on types
class TypeOps a where
    -- applies a substitution
    apply :: Subst -> a -> a

    -- finds free variables
    fv :: a -> [Var]

----------------------------------------
-- some basic instances

instance TypeOps Type where
    apply s (TVar v)	 = applySubst s v
    apply s t@(TCon _)	 = t
    apply s (TApp t1 t2) = TApp (apply s t1) (apply s t2)

    fv t = nub (f [] t)
      where
	f a (TVar v)	 = v:a
	f a (TCon _)	 = a
	f a (TApp t1 t2) = f (f a t2) t1

-- NOTE: apply on vars is non-standard
instance TypeOps Var where
    apply s = headMsg "no variables!" . fv . apply s . TVar
    fv      = (:[]) 

instance TypeOps a => TypeOps [a] where
    apply s xs = List.map (apply s) xs
    fv xs      = nub (concatMap fv xs)

instance (TypeOps a, TypeOps b) => TypeOps (a,b) where
    apply s (a, b) = (apply s a, apply s b)
    fv (a, b)	   = nub (fv a ++ fv b)

instance (TypeOps a, TypeOps b, TypeOps c) => TypeOps (a,b,c) where
    apply s (a, b, c) = (apply s a, apply s b, apply s c)
    fv (a, b, c)      = nub (fv a ++ fv b ++ fv c)

instance (TypeOps a, TypeOps b, TypeOps c, TypeOps d) => TypeOps (a,b,c,d) where
    apply s (a, b, c, d) = (apply s a, apply s b, apply s c, apply s d)
    fv (a, b, c, d)	 = nub (fv a ++ fv b ++ fv c ++ fv d)

-- A bit of a hack. (Used by Core.Inference where we apply fv to a list of
-- string, type pairs.)
instance TypeOps Char where
    fv _ = []
    apply s c = c

-- rename something in a monad with a number supply
rename :: (HasNumSupply m, TypeOps a) => a -> m a
rename x = return . flip apply x =<< renameSubst x

----------------------------------------
-- Substitutions

-- maps variables to types
-- type Subst = FiniteMap Var Type
type Subst = Map Var Type

-- idSubst = emptyFM
idSubst = empty

applySubst :: Subst -> Var -> Type
-- applySubst s v = case lookupFM s v of
applySubst s v = case Data.Map.lookup v s of
    Nothing -> TVar v
    Just t  -> t

buildSubst :: [(Var,Type)] -> Subst
-- buildSubst = listToFM
buildSubst = fromList

renameSubst :: (HasNumSupply m, TypeOps a) => a -> m Subst
renameSubst a = do 
    let vs = fv a
    ts <- mapM newVar vs
--     return (listToFM (zip vs ts))
    return (fromList (zip vs ts))
  where
    -- NOTE: replacement variable has the same src. info
    newVar (Var (Name r s)) = do
	n <- freshInt
	let s' = 'v' : show n
	return (TVar (Var (Name r s')))

updateSubst :: Subst -> (Var, Type) -> Subst
--updateSubst s vt@(v,t) = addToFM s' v t
updateSubst s vt@(v,t) = Data.Map.insert v t s'
  where
    -- apply new mapping to old subst
--    s' = mapFM (\k -> apply vt) s
    s' = Data.Map.mapWithKey (\k -> apply vt) s

    -- use this to avoid building a single-element FM
    apply :: (Var, Type) -> Type -> Type
    apply (v,t) tv@(TVar x) | x == v    = t
			    | otherwise = tv
    apply vt    c@(TCon _)	  = c
    apply vt    (TApp t1 t2)	  = TApp (apply vt t1) (apply vt t2)


-- combines two substitutions
composeSubst :: Subst -> Subst -> Subst
-- composeSubst s1 s2 = foldl updateSubst s2 (fmToList s1)
composeSubst s1 s2 = foldl updateSubst s2 (toList s1)

--------------------------------------------------------------------------------

-- gives variables more palatable names
prettyRename :: TypeOps a => a -> a
prettyRename = prettyRenamer fv alphaStrings

prettyRenameExplicitFV :: TypeOps a => (a -> [Var]) -> a -> a
prettyRenameExplicitFV fv = prettyRenamer fv alphaStrings

-- as above, but variables are uppercase
prettyRenameUpper :: TypeOps a => a -> a
prettyRenameUpper = prettyRenamer fv (List.map (List.map toUpper) alphaStrings)

prettyRenamer :: TypeOps a => (a -> [Var]) -> [String] -> a -> a
prettyRenamer fv ns x = apply s x
  where
    s = let vs = fv x
	    ts = List.map (TVar . mkVar) ns
--	in  listToFM (zip vs ts)
	in  fromList (zip vs ts)

--------------------------------------------------------------------------------
-- miscellaneous operations on types

-- if the given type is a tuple, return the elements of that tuple type, 
-- else Nothing
tupleTypes :: Type -> Maybe [Type]
tupleTypes t = do lc <- tts t
		  return (lc [])
    where   tts :: Type -> Maybe ([Type] -> [Type])
	    tts (TApp (TCon tc) t1)
		| isTupleCon (nameStr tc) = return ([t1]++)
		| otherwise     = Nothing
	    tts (TApp t1 t2) = do lc <- tts t1
				  return ((lc [t2])++)
	    tts (TCon tc) | nameStr tc == tupleName 0 = return (const [])
	    tts _ = Nothing

-- True if the given name represents a tuple constructor
isTupleCon :: IdStr -> Bool
isTupleCon = isJust . tupleArity

-- arity of the named tuple
tupleArity :: IdStr -> Maybe Int
tupleArity id = do
    when (head id /= '(') (fail "")
    when (last id /= ')') (fail "")
    if and [ b | x <- (init.tail) id, let b = x == ',']
       then return (length id - 2)
       else Nothing

-- NOTE: this is copied directly from BuiltIn! Importing that module would
--       lead to a cycle.
tupleName = tupleStr  
tupleStr n = ("(" ++ replicate (n-1) ',' ++ ")")


isTuple :: Type -> Bool
isTuple t = isJust (tupleTypes t)

-- can't use listStr, or we'd have a module cycle (Types <-> BuiltIn )
isList :: Type -> Bool
isList (TApp (TCon nm) _) = nameStr nm == "[]" -- listStr
isList _ = False


-- returns a list of all the names of constructors in the type
typeTCons :: Type -> [Name]
typeTCons t = f [] t
  where
    f a (TVar _) = a
    f a (TCon n) = n : a
    f a (TApp t1 t2) = f (f a t2) t1

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-

hasSrcId NoSrcId   = False
hasSrcId (SrcId _) = True

-- builds a substitution which replaces the name string of variables with their 
-- source id (name number remains)
revealSrcIdSubst [] = idSubst
revealSrcIdSubst (tv:tvs) = 
    let sid = tvarSrcId tv
	id  = srcId sid
	l   = nameNum (tvarName tv)
	t   = Var (tv { tvarName = name id l })
	    
	phi = revealSrcIdSubst tvs
    in  if hasSrcId sid then updateSubst phi tv t
			else phi

unVar (Var tv) = tv
unVar t	       = error ("TD_Types.unVar: not a var: " ++ show t)

unVar' _ (Var tv) = tv
unVar' s t	 = error ("TD_Types.unVar: not a var: " ++ s ++ " " ++ show t)

isVar (Var _) = True
isVar _       = False
isTApp (TApp _ _) = True
isTApp _          = False
isTyCon (TyCon _) = True
isTyCon _	  = False

-- True if the given type is a list
isList (TApp (TyCon n) _) = n == nilName
isList _ = False

-- True if the given type is a tuple (of any arity)
isTuple t = isJust (tupleTypes t)

-- true if the type contains no variables
isGround :: Type -> Bool
isGround (Var _)   = False
isGround (TyCon _) = True
isGround (TApp t1 t2) = isGround t1 && isGround t2

vars = map Var

-- ignores location
nubTVars = fv . nub . vars

instance Show TVar where
    show (TVar n l id) | id == NoSrcId = show n -- ++ "." ++ show l 
		       | otherwise = show n ++ "(/" ++ srcId id ++ ")."++ show l

instance Eq Type where
    (Var tv1)    == (Var tv2)    = tvarName tv1 == tvarName tv2
    (TyCon c1)   == (TyCon c2)   = c1 == c2
    (TApp t1 t2) == (TApp t1' t2') = t1 == t1' && t2 == t2'
    _		 == _		   = False



newVarLoc :: Loc -> TVar -> TVar
newVarLoc l tv = tv { tvarLoc = l }

typeLocs :: Type -> [Loc]
typeLocs t = map tvarLoc (fv t)


-- Primitive types

-- note: variable numbers -19 to -8 are left available
arrowName       = name "->" 0
listName	= nilName
nilName         = name "[]" (-1)
consName	= name ":"  (-2)
catName         = name "++" (-3)
trueName	= name "True"  (-4)
falseName	= name "False" (-5)
boolName	= name "Bool"  (-6)
undefinedName	= name "undefined" (-7)

vnilName	= name "|" (-8)
vconsName	= name "\\" (-9)

tupleName arity = name ("(" ++ replicate (arity-1) ',' ++ ")")
		       (fromIntegral (-(arity+20)))

-- all skolem function names begin with this string
skString = "Sk!"

-- returns the names of all constructors appearing in the given type
tconsInType t = tc [] t
  where
    tc a (Var _) = a
    tc a (TyCon t) = t:a
    tc a (TApp t1 t2) = tc (tc a t1) t2


isMultiCon :: Name -> Bool
isMultiCon = isJust . multiArity
 
multiArity :: Name -> Maybe Int
multiArity name = do
    case nameStr name of
	'{':xs -> let (n,r) = span isDigit xs
		  in  case r of
			"}" -> return (read n)
			_   -> Nothing
	_ -> Nothing
    
    


-- as above, but for multiple types represented as one
multiTypes :: Type -> Maybe [Type]
multiTypes t = do lc <- mts t
		  return (lc [])
    where   mts :: Type -> Maybe ([Type] -> [Type])
	    mts (TApp (TyCon tc) t1)
		| isMultiCon tc = return ([t1] ++ )
		| otherwise     = fail ""
	    mts (TApp t1 t2) = do lc <- mts t1
				  return ((lc [t2]) ++ )
	    mts (TyCon tc) | tc == multiTypeName 0 = return (const [])
	    mts _ = fail ""



-- Substitutions

type Subst = [(TVar,Type)]

idSubst :: Subst
idSubst = []

-- The state
type State = Integer

-- State monad for new variable supply
data TP a = TP (State -> E (State,a))
 

-------------------------------------
-- Class and instance declarations --
-------------------------------------


class TC a where
   apply :: Subst -> a -> a
   fv :: a -> [TVar]
   occurs :: TVar -> a -> Bool 
   rename :: a -> TP a
   format :: a -> String

   -- default methods (for deprecated functions)
   format = error "BUG: don't use TC method `format'"


unTP (TP a) = a
instance Monad TP where
   m >>= k  = TP ( \ s -> case ((unTP m) s) of 
                            Succ (s',x) -> unTP (k x) s'
                            Err e       -> Err e )
   return x = TP ( \ s -> Succ (s,x) )

instance TC a => TC [a] where
   apply s = map (apply s)
   fv x = foldl f [] x 
           where
            f z y = z ++ (fv y)        -- note there might duplicate variables
   occurs v x = foldl f False x 
                 where
                   f z y = z || (occurs v y)
   rename x = do s <- renameSubst (fv x)
                 return (apply s x)
   format xs = f xs
                    where
		     f [] = ""
		     f [x] = (format x)
		     f (x:xs) = (format x) ++ ", " ++ (f xs)

instance TC TVar where
    apply s v = let t = apply s (Var v)
		in  if isVar t then unVar t
		    else error "BUG: can't applying subst. to var gives type!"
    fv v = [v]
    occurs = (==)
    rename v = renameSubst [v] >>= \s -> return (apply s v)
    format = error "BUG: don't use TC method `format' on TVar"
		      

instance (TC a, TC b) => TC (a, b) where
    apply s (a, b) = (apply s a, apply s b)
    fv (a, b) = fv a ++ fv b
    occurs v (a, b) = occurs v a || occurs v b
    rename ab = renameSubst (fv ab) >>= \s -> return (apply s ab)
    format = error "BUG: don't use TC method `format' on (a,b)"
    
instance (TC a, TC b, TC c) => TC (a, b, c) where
    apply s (a, b, c) = (apply s a, apply s b, apply s c)
    fv (a, b, c) = fv a ++ fv b ++ fv c
    occurs v (a, b, c) = occurs v a || occurs v b || occurs v c
    rename abc = renameSubst (fv abc) >>= \s -> return (apply s abc)
    format = error "BUG: don't use TC method `format' on (a,b,c)"


instance (TC a, TC b, TC c, TC d) => TC (a, b, c, d) where
    apply s (a, b, c, d) = (apply s a, apply s b, apply s c, apply s d)
    fv (a, b, c, d) = fv (a,b) ++ fv (c,d)
    occurs v (a, b, c, d) = occurs v (a,b) || occurs v (c,d)
    rename abcd = renameSubst (fv abcd) >>= \s -> return (apply s abcd)
    format = error "BUG: don't use TC method `format' on (a,b,c,d)"


-- instances of TC for other "container" types follow

instance TC a => TC (Coloured a) where
    apply s ca = ca { colourised = apply s (colourised ca) }
    fv ca = fv (colourised ca)
    occurs tv ca = occurs tv (colourised ca)
    rename ca = renameSubst (fv ca) >>= \s -> return (apply s ca)
    format = error "BUG: don't use TC method `format' on `Coloured' things"

instance PPrint Type where
    pprint t = return (text (show t))

instance Show Type where
    -- prec 0: infix
    -- prec 1: application
    -- prec 2: atomic
    showsPrec n (Var tv) ss = show (tvarName tv) ++ ss
    showsPrec n (TyCon x) ss = infixParens (show x) ++ ss
    showsPrec n t@(TApp t1 t2) ss =
	let no_con =
	     if n > 1
		then '(' : showsPrec 1 t1 (" " ++ showsPrec 2 t2 (')' : ss))
		else showsPrec 1 t1 (" " ++ showsPrec 2 t2 ss)
	    non_lst =  let mts = tupleTypes t 
			   ts  = fromJust mts
			   mms = multiTypes t
			   ms  = fromJust mms
		       in  if isNothing mts
			      then if isNothing mms
				   then no_con
				   else unwords (map show ms) ++ ss
			      else '(': Term.uncommas (map show ts) ++ ")" ++ ss
	in case t1 of
	    (TApp (TyCon (Name ("->",_))) t1) ->
		if n > 0
		then '(' : showsPrec 1 t1 (" -> " ++ showsPrec 0 t2 (')' : ss))
		else showsPrec 1 t1 (" -> " ++ showsPrec 0 t2 ss)
	    
	    (TyCon name) | name == nilName -> "[" ++ show t2 ++ "]" ++ ss
--			 | otherwise       -> non_lst
	    t1 -> non_lst
		  

showTypeLoc x = showTypeLocPrec 0 x ""
showTypeLocPrec n (Var tv) ss = "t" ++ show (tvarLoc tv) ++ ss
showTypeLocPrec n (TyCon x)   ss = show x ++ ss
showTypeLocPrec n t@(TApp t1 t2) ss =
	let no_con =
	     if n > 1
		then '(' : showTypeLocPrec 1 t1 (" " ++ showTypeLocPrec 2 t2 (')' : ss))
		else showTypeLocPrec 1 t1 (" " ++ showTypeLocPrec 2 t2 ss)
	    non_lst =  let mts = tupleTypes t 
			   ts  = fromJust mts
		       in  if isNothing mts
			      then no_con
			      else '(': Term.uncommas (map (\x -> showTypeLocPrec 0 x "") ts) ++ ")" ++ ss
	in case t1 of
	    (TApp (TyCon (Name ("->",_))) t1) ->
		if n > 0
		then '(' : showTypeLocPrec 1 t1 (" -> " ++ showTypeLocPrec 0 t2 (')' : ss))
		else showTypeLocPrec 1 t1 (" -> " ++ showTypeLocPrec 0 t2 ss)
	    
	    (TyCon name) -> if name == nilName 
			       then "[" ++ showTypeLocPrec 0 t2 "" ++ "]" ++ ss
			       else non_lst
	    t1 -> non_lst
	  
		  

instance TC Type where
   apply s (Var v) = lookupVar s v
   apply s (TyCon tc) = TyCon tc 
   apply s (TApp t1 t2) = TApp (apply s t1) (apply s t2)
   fv (Var v) = [v]
   fv (TyCon _) = []
   fv (TApp t1 t2) = nub $ (fv t1) ++ (fv t2)
   occurs v (Var v') = if (tvarName v) == (tvarName v') then True else False
   occurs v (TyCon _) = False
   occurs v (TApp t1 t2) = (occurs v t1) || (occurs v t2)
   rename t = do s <- renameSubst (fv t)
                 return (apply s t)
   format = show


-- we impose an order on types
-- variables less than anything
instance Ord Type where
 (<) (Var tv1) (Var tv2) = tvarName tv1 < tvarName tv2
 (<) (Var _) _ = True
 (<) (TyCon x) (TyCon y) = (x < y) 
 (<) (TApp t1 t2) (TApp t1' t2') = if t1 == t1' then t2 < t2'
                                   else t1 < t1' 
 (<) _ _ = False

instance Ord TVar where
    tv1 < tv2 = tvarName tv1 < tvarName tv2


---------------
-- Functions --
---------------


-- lookup, update Substitutions 

lookupVar :: Subst -> TVar -> Type
lookupVar [] v = Var v
lookupVar ((v,t):s) v'
   | tvarName v == tvarName v' = t
   | otherwise		       = lookupVar s v'


updateSubst :: Subst -> TVar -> Type -> Subst
updateSubst s v t = (v,t):(map f s)
     where 
       f (v',t') = (v',apply [(v,t)] t')

-- new variable or type name, renaming types

newTVar :: TP TVar
newTVar = TP (\n -> return (n+1, origTVar (name ("a"++(show n)) n) noLoc))

newTCon :: String -> TP TCon
newTCon id = TP (\n -> return (n+1, name id n))

newInteger :: TP Integer
newInteger = TP (\n -> return (n+1,n))



-- compute renaming substitution for set vs of variables

-- maintains the original location of the renamed variable
renameSubst :: [TVar] -> TP Subst
renameSubst vs = let rensubst = foldl f (return idSubst) vs
                     f z y@(TVar _ l id) = do 
				s <- z
				tv' <- newTVar
				let y' = TVar (tvarName tv') l id
				return (updateSubst s y (Var y'))
                 in rensubst 


-- in addition we return the set of all freshly created variables

renameSubst2 :: [TVar] -> TP (Subst,[TVar])
renameSubst2 vs = let rensubst = foldl f (return (idSubst,[])) vs
                      f z y = do (s,ns) <- z
                                 n <- newTVar
                                 return (updateSubst s y (Var n),n:ns)
                  in rensubst 

 
-- substitution will be threaded through
-- tvs is a list of variables which should not be substituted
-- by another type variable not contained in tvs

unify :: [TVar] -> Subst -> [(Type,Type)] -> E Subst
unify tvs subst ts = foldl f (return subst) ts
   where
     f z (t1,t2) = do s <- z
                      s' <- unify' (s, apply s t1, apply s t2)
                      return s'
     -- substitution will be threaded through
     -- assumption: substitution is already applied to types
     tvarNotElem tv tvs = tvarName tv `notElem` (map tvarName tvs)
     unify' :: (Subst, Type, Type) -> E Subst
     unify' (s, Var x, Var y) = 
               if tvarName x == tvarName y then return s
               else if tvarNotElem x tvs then return (updateSubst s x (Var y))   -- this is crucial !!
                    else return (updateSubst s y (Var x))
     unify' (s, Var x, t) =
               if (occurs x t) then errorE ("occurs check " ++ show t) idSubst
               else return (updateSubst s x t)  
     unify' (s, t, Var x) = unify' (s, Var x, t)
     unify' (s, TyCon tc1, TyCon tc2) =
         if tc1 /= tc2 then errorE ("no mgu 1: " ++ show tc1 ++ " " ++ show tc2) idSubst
         else return s
     unify' (s, TApp t1 t2, TApp t1' t2') = 
         do s' <- unify' (s, t1, t1')
            unify' (s', apply s' t2, apply s' t2') 
     unify' (s, _, _) = errorE "no mgu 2" idSubst

     
-- as above, but keeps identity substitutions (ie. x |-> x)
unifyWithIds :: [TVar] -> Subst -> [(Type,Type)] -> E Subst
unifyWithIds tvs subst ts = foldl f (return subst) ts
   where
     f z (t1,t2) = do s <- z
                      s' <- unify' (s, apply s t1, apply s t2)
                      return s'
     -- substitution will be threaded through
     -- assumption: substitution is already applied to types
     tvarNotElem tv tvs = tvarName tv `notElem` (map tvarName tvs)

     unify' :: (Subst, Type, Type) -> E Subst
     unify' (s, Var x, Var y) = 
               -- if (fst x) == (fst y) then return s
               --else 
	       if tvarNotElem x tvs 
		  then let s1 = updateSubst s x (Var y)
		       in  return (updateSubst s1 y (Var y))
                  else let s1 = updateSubst s y (Var x)
		       in  return (updateSubst s1 x (Var x))
     unify' (s, Var x, t) =
               if (occurs x t) then errorE ("occurs check " ++ show t) idSubst
               else return (updateSubst s x t)  
     unify' (s, t, Var x) = unify' (s, Var x, t)
     unify' (s, TyCon tc1, TyCon tc2) =
         if tc1 /= tc2 then errorE "no mgu" idSubst
         else return s
     unify' (s, TApp t1 t2, TApp t1' t2') = 
         do s' <- unify' (s, t1, t1')
            unify' (s', apply s' t2, apply s' t2') 
     unify' (s, _, _) = errorE "no mgu" idSubst


-- variation of unify
-- we assume that variables in tvs are fixed, i.e. are not allowed to be 
-- substituted
unifyTypes :: [TVar] -> Subst -> [(Type,Type)] -> E Subst
unifyTypes tvs subst ts = foldl f (return subst) ts
   where
     f z (t1,t2) = do s <- z
                      s' <- unify' (s, apply s t1, apply s t2)
                      return s'
     -- substitution will be threaded through
     -- assumption: substitution is already applied to types
     unify' :: (Subst, Type, Type) -> E Subst
     unify' (s, Var x, Var y) = 
               if x == y then return s
               else if notElem x tvs then return (updateSubst s x (Var y))   -- this is crucial !!
                    else if notElem y tvs then return (updateSubst s y (Var  x)) -- again
                         else errorE "fail: variable is fixed" idSubst
     unify' (s, Var x, t) =
               if (occurs x t) then errorE "fail: occurs check" idSubst
               else if notElem x tvs then return (updateSubst s x t)  
                    else errorE "fail: variable is fixed" idSubst
     unify' (s, t, Var x) = unify' (s, Var x, t)
     unify' (s, TyCon tc1, TyCon tc2) =
         if tc1 /= tc2 then errorE "fail: no mgu" idSubst
         else return s
     unify' (s, TApp t1 t2, TApp t1' t2') = 
         do s' <- unify' (s, t1, t1')
            unify' (s', apply s' t2, apply s' t2') 
     unify' (s, _, _) = errorE "fail: no mgu" idSubst


--------------------------------------------------------------------------------

-- assumption both lists are of equal size
-- we match elements at the same position
-- matchTypes ts1 ts2 = True if there's phi s.t. phi ts1 = ts2
matchTypes :: [Type] -> [Type] -> Bool
matchTypes [] [] = True
matchTypes ts1 ts2 = let vars (Var v) vs= if elem v vs then vs 
                                          else v:vs
                         vars (TyCon _) vs = vs
                         vars (TApp t1 t2) vs = let vs'= vars t1 vs
                                                in vars t2 vs'
                         varss [t] vs = vars t vs
                         varss (t:ts) vs = let vs' = vars t vs
                                           in varss ts vs'
                         skconst (Var tv)  = tvarName tv
                         skconst (TyCon c) = c
                         skconst (TApp t1 t2) = max (skconst t1) (skconst t2)
                         skconsts [t] = skconst t
                         skconsts (t:ts) = max (skconst t) (skconsts ts)
                         sk = skconsts (ts1++ts2)
                         vs = varss (ts2) []
                         (skolemsubst,_) = foldl f (idSubst, incName sk) vs
                         f (subst,sk) v = (updateSubst subst v (TyCon sk), incName sk)
                         ts2'= apply skolemsubst ts2
                     in case (unify [] idSubst (zip ts1 ts2')) of
                         Succ _ -> True
                         Err  _ -> False 

-- matchTypes2 vs s1 t1 t2 = s2
-- find renaming substitution s2 (for v not in vs) such that t1 = s t2
-- otherwise report failure
matchTypes2 :: [TVar] -> Subst -> [Type] -> [Type] -> E Subst
matchTypes2 vs s [] [] = return s 
matchTypes2 vs s ts1 ts2 = foldl f (return s) (zip ts1 ts2)
  where
    f z (t1,t2) = do s <- z
                     s' <- matchType2 vs s t1 (apply s t2)
                     return s'       
    matchType2 :: [TVar] -> Subst -> Type -> Type -> E Subst
    matchType2 vs s (Var x) (Var y) = 
                     if x == y then return s
                     else if (notElem y vs) then return (updateSubst s y (Var x))
                          else Err "no renaming found (0)"
			      
    matchType2 vs s t (Var y) = 
                     if (notElem y vs) then return (updateSubst s y t)
                     else Err "no renaming found (1)"

    matchType2 vs s (TyCon tc1) (TyCon tc2) = if tc1 == tc2 then return s
                                              else Err "no renaming found (2)"
    matchType2 vs s (TApp t1 t2) (TApp t1' t2') =
                do s' <- matchType2 vs s t1 t1'
                   matchType2 vs s' t2 (apply s' t2')
    matchType2 _ _ _ _ = Err "no renaming found (3)"


-- signal whether there exists renaming phi such that phi ts1 = ts2
matchTypes3 :: [Type] -> [Type] -> Bool
matchTypes3 ts1 ts2 = case (matchTypes2 [] idSubst ts1 ts2) of
                       Succ _ -> True
                       Err _ -> False

-- report error

-- x is default parameter, thrown away in the current implementation
errorTP :: Show a => String -> a -> TP a
errorTP text x = TP (\n -> Err msg) 
    where msg = text ++ "\n" 


-- x is default parameter, thrown away in the current implementation
errorE :: String -> a -> E a
errorE text x = Err text


--------------------------------------------------------------------------------
-- builds a renaming subst. for the given type vars; to give them more
-- palatable names

-- does two things:
--  - restores the original source names of type variables
--  - renames all new/internal variables (avoiding clashes with existing names)
simpTVarSubst :: [TVar] -> Subst
simpTVarSubst tvs = ren tvs typs
  
    where
	-- first list contains vars to rename, second is the new name supply 
	ren [] _ = []
	ren (tv:tvs) tts@(t:ts) 
	    | hasSrcId (tvarSrcId tv) = (tv, Var tv) : ren tvs tts
	    | otherwise = (tv, t) : ren tvs ts
    
	typs = map (\id -> Var (origTVar (name id 0) noLoc)) okayStrs

	okayStrs = filter (`notElem`srcIds) newStrs
    
	srcIds = concatMap (\tv -> let sid = tvarSrcId tv
				   in  if hasSrcId sid then [srcId sid]
						       else []) tvs
	newStrs = "a" : map incStr newStrs
    
	incStr ""  = "a"
	incStr str = let (c:cs) = reverse str
			 str'   = reverse (succ c : cs)
		     in  doCarry str'

	-- while last char. is > 'z', set to 'a' and inc. the prefix
	doCarry str = let (c:cs) = reverse str
		      in  if c > 'z'
			     then reverse ('a' : (incStr (reverse cs)))
			     else str


presentableVars :: TC a => a -> a
presentableVars a = let vs = nub (fv a)
			phi = simpTVarSubst vs
		    in  apply phi a


  -}
