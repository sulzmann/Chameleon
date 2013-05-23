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
-- Kind inference
--
--------------------------------------------------------------------------------

module Core.Kinds.Inference (
   kindValidate
) where

import Char
import List
import Maybe
import Monad

import qualified Core.BuiltIn as BuiltIn
import Core.Constraint
import Core.CHR
import Core.Justify
import Core.InfGoal
import Core.InfResult
import qualified Core.Solver as Inf
import Core.Types 
import Core.Name
import Core.ConsOps

import AST.Common
import qualified AST.Internal as AST
import AST.SrcInfo

import Misc
import Misc.Pretty

import TypeError.ErrorMsg
import Misc.Error
import Misc.Print

----------------------------------------------------------------------------------
-- Definition of Kinds
----------------------------------------------------------------------------------

type Kind = Type

star = "*"
starTCon = TCon (mkFreeName star)

-- Make Default kind of n arguments
makeDKind :: Int -> Kind
makeDKind 0 = TCon (mkFreeName star)
makeDKind n = let arr = TCon (mkFreeName "->")
              in TApp (TApp arr (TCon (mkFreeName star))) (makeDKind (n-1))

-- Make polymorphic kind from list of kind arguments
makePKind :: [Kind] -> Kind
makePKind []     = TCon (mkFreeName star)
makePKind (x:xs) = let arr = TCon (mkFreeName "->")
                   in TApp (TApp arr x) (makePKind xs)

convertToKind :: AST.Type -> KTR (Maybe Kind)
convertToKind (AST.ConType id) = case (idStr id) of
                                   "*"  -> return (Just starTCon)
                                   "->" -> return (Just (TCon (mkFreeName "->")))
                                   _    -> return Nothing
convertToKind (AST.VarType _)  = do k <- newKindVar
                                    return (Just k)
convertToKind (AST.AppType _ t1 t2) = do mb1 <- convertToKind t1
                                         mb2 <- convertToKind t2
                                         case mb1 of
                                           Just k1 -> case mb2 of
                                                        Just k2 -> return (Just (TApp k1 k2))
                                                        _       -> return Nothing
                                           _       -> return Nothing

---------------------------------------------------------------------------------
-- Built-in CHRs and Kind Representation
---------------------------------------------------------------------------------

-- Builtin Type Constructors

intCons     = "Int"
floatCons   = "Float"
doubleCons  = "Double"
integerCons = "Integer"
boolCons    = "Bool"
charCons    = "Char"
strCons     = "String"
trueCons    = "intT1!"
starCons    = "*"
barCons     = "|"

listCons  = "[]"
funcCons  = "->"
emptCons  = "()"
tupleCons n = "(" ++ (replicate (n-1) ',')  ++ ")"

numClass  = "Num"
fracClass = "Fractional"

-- Check if a type constructor is an n-tuple 
isTupleKind :: [Char] -> Bool
isTupleKind x = (nub x) == "(,)"

-----------------------------------------------------
-- Type Constructor Environment
-----------------------------------------------------

data EnvRes = EnvRes { envId :: Id, envKind :: Kind }

data Env = Env { envNodes :: [EnvRes] }

instance Show EnvRes where
    show (EnvRes id k) = "(" ++ (idStr id) ++ "::" ++ (show k) ++ ")"

instance Show Env where
    show (Env en) = show en

instance Pretty EnvRes where
    pretty (EnvRes id k) = "(" ++ (idStr id) ++ "::" ++ (pretty k) ++ ")"

instance Pretty Env where
    pretty (Env rs) = "[" ++ (pretty rs) ++ "]"

emptyEnv = Env []

------------------------------------------------------
-- Procedures for looking up and extending Environment

envNodes' f env = env { envNodes = f (envNodes env) }

-- Misc function, unions two Envs. Warning! Intersections of Envs should be empty. 
unionEnvs :: Env -> Env -> Env
unionEnvs (Env rs1) (Env rs2) = Env (rs1 ++ rs2)

extendEnvInt :: Env -> EnvRes -> Env
extendEnvInt env x = envNodes' (x:) env

extendEnv :: Id -> Kind -> Env -> Env
extendEnv id k env = let mb = lookupEnv (idStr id) env
                     in case mb of
                          Nothing -> extendEnvInt env (EnvRes id k)
                          _       -> let env' = Env (removeId id (envNodes env))
                                     in extendEnvInt env' (EnvRes id k)

removeId :: Id -> [EnvRes] -> [EnvRes]
removeId id (r:rs) = let id' = envId r
                     in case (idStr id) == (idStr id') of
                          True  -> rs
                          False -> r:(removeId id rs)
removeId id []     = []

extendEnvL :: [Id] -> [Kind] -> Env -> Env
extendEnvL (id:ids) (k:ks) env = let env' = extendEnv id k env
                                 in extendEnvL ids ks env'
extendEnvL [] [] env           = env
extendEnvL _  _ env            = error "Bug: Wrong usage of extendEnvL"

lookupEnv :: IdStr -> Env -> Maybe EnvRes
lookupEnv str env = let xs = filter ((==str) . (idStr . envId)) (envNodes env)
                       in listToMaybe xs

getEnvIds :: Env -> [Id]
getEnvIds (Env res) = map envId res

-----------------------------------------------
-- Built in constructor environment

-- make a default environment mapping
-- makeDRes id n = id :: (* -> ... -> * (x n-1))
makeDRes :: String -> Int -> EnvRes
makeDRes id n = EnvRes (anonId id) (makeDKind n)

makeDResL :: [String] -> [Int] -> [EnvRes]
makeDResL (id:ids) (n:ns) = let envres = makeDRes id n
                            in envres:(makeDResL ids ns)
makeDResL [] []           = []
makeDResL _ _             = error "Bug: Wrong Usage of makeDResL"

builtInIds = [doubleCons,intCons,floatCons,integerCons,boolCons,charCons,strCons,listCons,funcCons,emptCons,numClass,fracClass,starCons,barCons]

builtInNs = [0,0,0,0,0,0,0,1,2,0,1,1,1,2]

builtInEnv = Env (makeDResL builtInIds builtInNs) 

-----------------------------------------------------
-- Constraint Environment (id :: Constraint)
-----------------------------------------------------

data CEnvRes = CEnvRes { cEnvId :: Id, cEnvCons :: Constraint }

data CEnv = CEnv { cEnvNodes :: [CEnvRes] }

instance Pretty CEnvRes where
    pretty (CEnvRes id con) = "(" ++ (idStr id) ++ "::" ++ (pretty con) ++ ")"

instance Pretty CEnv where
    pretty (CEnv rs) = "[" ++ (pretty rs) ++ "]"

emptyCEnv = CEnv []

------------------------------------------------------
-- Procedures for looking up and extending Environment

cEnvNodes' f env = env { cEnvNodes = f (cEnvNodes env) }

extendCEnvInt :: CEnv -> CEnvRes -> CEnv
extendCEnvInt env x = cEnvNodes' (x:) env

extendCEnv :: Id -> Constraint -> CEnv -> CEnv
extendCEnv id con env = extendCEnvInt env (CEnvRes id con)

extendCEnvL :: [Id] -> [Constraint] -> CEnv -> CEnv
extendCEnvL (id:ids) (con:cons) env = let env' = extendCEnv id con env
                                      in extendCEnvL ids cons env'
extendCEnvL [] [] env               = env
extendCEnvL _  _ env                = error "Bug: Wrong usage of extendEnvL"

lookupCEnv :: IdStr -> CEnv -> Maybe CEnvRes
lookupCEnv str env = let xs = filter ((==str) . (idStr . cEnvId)) (cEnvNodes env)
                     in listToMaybe xs

getCEnvIds :: CEnv -> [Id]
getCEnvIds (CEnv res) = map cEnvId res 

extractCons :: CEnv -> [IdStr] -> Constraint
extractCons cenv (id:ids) = let mb = lookupCEnv id cenv
                            in case mb of
                                 Just (CEnvRes _ cons) -> cons /\ (extractCons cenv ids)
                                 Nothing               -> extractCons cenv ids
extractCons _ []          = trueConstraint

mergeAllCons :: CEnv -> Constraint
mergeAllCons (CEnv cenvres) = let cons = map cEnvCons cenvres
                              in foldl (/\) trueConstraint cons

--------------------------------------------------------------------------------------------------------
-- Kind Transition Monad - KTR
--------------------------------------------------------------------------------------------------------

data KState = ST { num     :: Int,        -- Variable Index Iterator
                   bEnv    :: Env,        -- Builtin Constructor Environment
                   kEnv    :: Env,        -- Visible kind Environment
                   polys   :: Env,        -- Polymorphic Constructor Environment
                   conUniv :: Constraint, -- Constraint Universe of Program
                   dGraph  :: Graph,      -- Dependency Graph of Program
                   conEnv  :: CEnv,       -- Constraint Environment for Mimic GHC mode
                   infG    :: [InfGoal],  -- Inference Goals
                   options :: Bool,       -- solver options, True for Mimic GHC
                   debug   :: Bool }      -- Internal debugging toggle
                   --skTest  :: Constraint} -- Test Constraint set 

-- build a default KState with mimic GHC boolean toggle.
defaultKState :: Bool -> KState
defaultKState b = ST 0 builtInEnv emptyEnv emptyEnv trueConstraint emptyGraph emptyCEnv [] b False

-- Function that prepares the final KState of the principal inference procedures, for the next stage
-- of GHC kind validation. receives an ENV kenv', assumed to be the results of the inference process
-- and replaces kenv as the visible kind environment. kenv is instead placed in the ploymorphic
-- constructor environment. Final Original inference goals are emptied away.
-- PS :: This hacky function is no longer in use.
prepState :: Env -> KState -> KState
prepState kenv' (ST i benv kenv _ cU dG cenv _ opt de) = ST i benv kenv' kenv cU dG cenv [] opt de

instance Pretty KState where
   pretty (ST i env1 env2 env3 c g _ infGs _ _) = 
       "{" ++ (show i) ++ "\nBuiltin:" ++ (pretty env1) ++ "\nUserDefined:" ++ (pretty env2) ++ "\nPolymorphic:" ++ (pretty env3) ++ "\nConstraint Universe:" ++ (pretty c) ++ "\nDependencies:" ++ (pretty g) ++ "\nInfGoals:" ++ (pretty infGs) ++ "}"

newtype KTR a = KTR (KState -> IO (E (a,KState)))

instance Monad KTR where         

    -- return :: a -> KTR a
    return a = KTR (\s -> return (Succ (a,s)))         

    -- (>>=)  :: KTR a -> (a -> KTR b) -> KTR b
    (KTR a) >>= f = KTR (\s -> a s >>= \r -> case r of
                                Succ (a',s') -> let KTR f' = f a' in f' s'
                                Err t        -> return (Err t))

    -- fail :: String -> KTR a
    fail e = failKTR e

failKTR e = KTR (\s -> return (Err e))

---------------------------
-- Unpacking the translator

scanError (Err str) = do putStr str
scanError (Succ _)  = do putStr "Success"

runKTR :: KState -> KTR a -> IO (E a)
runKTR state tr = do eres <- runKTRAll state tr
                     --scanError eres
                     return $ case eres of
                          Err  str   -> Err str
                          Succ (a,_) -> Succ a

runKTRAll :: KState -> KTR a -> IO (E (a, KState))
runKTRAll state (KTR f) = f state

doIO :: IO a -> KTR a      
doIO c = KTR (\st -> c >>= \r -> return (Succ (r, st)))

puts :: String -> KTR ()
puts = doIO . putStrLn

doNothing :: KTR ()
doNothing = return ()

speak :: String -> KTR()
speak str = do debugMode <- ktrGet debug
               case debugMode of
                  True  -> puts str
                  False -> doNothing

getState :: KTR String
getState = do st <- ktrGet ident
              return (pretty st)

ident x = x    

-- Misc function, executes procedure proc only if mimic GHC
-- solver mode is active
mimicGHC :: KTR () -> KTR ()
mimicGHC proc = do op <- ktrGet options
                   case op of
                      True  -> proc
                      False -> doNothing 

----------------------------------------------
-- Functions for lookingup and updating kstate

ktrGet f    = KTR (\st -> return $ Succ (f st, st))
ktrUpdate f = KTR (\st -> return $ Succ ((), f st))
ktrSet f x  = ktrUpdate $ f (const x)

num'     f st = st { num     = f (num st)     }
kEnv'    f st = st { kEnv    = f (kEnv st)    }
bEnv'    f st = st { bEnv    = f (bEnv st)    }
polys'   f st = st { polys   = f (polys st)   }       
conEnv'  f st = st { conEnv  = f (conEnv st)  }
infG'    f st = st { infG    = f (infG st)    }            
conUniv' f st = st { conUniv = f (conUniv st) }
dGraph'  f st = st { dGraph  = f (dGraph st)  }
--skTest'  f st = st { skTest  = f (skTest st)  }

--------------------------
-- Using Id Index Iterator

getNum = ktrGet num
incNum = ktrUpdate (num' (+1))
setNum n = ktrUpdate $ num' (const n)

next :: KTR Int
next = do n <- getNum 
          incNum
          return n

nextN :: Int -> KTR [Int]
nextN 0 = do return []
nextN 1 = do n <- next
             return [n]
nextN n = do x  <- next
             xs <- nextN (n-1)
             return (x:xs)

-------------------------------------
-- Axulliary procedures for KTR Monad

digits :: Int -> [Char]
digits 0 = ['0']
digits x = (digits (div x 10)) ++ [(intToDigit (rem x 10))]

newKindVar :: KTR Kind
newKindVar = do n <- next
                let newId = "K" ++ (digits n)
                return (TVar (mkVar newId))

newkVar :: Int -> KTR Kind
newkVar n = do let newId = "K" ++ (digits n)
               return (TVar (mkVar newId))

newKindVars :: Int -> KTR [Kind]
newKindVars n = do ns   <- nextN n
                   nVar <- mapM newkVar ns
                   return nVar

------------------------------------------------------
-- Procedures for looking up and extending Environment

lookupCons :: IdStr -> KTR (Maybe EnvRes)
lookupCons id = do kenv <- ktrGet kEnv
                   let xs = filter ((==id) . (idStr . envId)) (envNodes kenv)
                   let mb = (listToMaybe xs)
                   case mb of
                      Just res -> return (Just res)
                      _        -> return Nothing

lookupBuiltIn :: IdStr -> KTR (Maybe EnvRes)
lookupBuiltIn id = do benv <- ktrGet bEnv
                      let xs = filter ((==id) . (idStr . envId)) (envNodes benv)
                      let mb = (listToMaybe xs)
                      case mb of
                         Just res -> return (Just res)
                         _        -> return Nothing

lookupPolys :: IdStr -> KTR (Maybe EnvRes)
lookupPolys id = do penv <- ktrGet polys
                    let xs = filter ((==id) . (idStr . envId)) (envNodes penv)
                    let mb = (listToMaybe xs)
                    case mb of
                       Just res -> return (Just res)
                       _        -> return Nothing

lookupConEnv :: IdStr -> KTR (Maybe CEnvRes)
lookupConEnv id = do cenv <- ktrGet conEnv
                     let xs = filter ((==id) . (idStr . cEnvId)) (cEnvNodes cenv)
                     let mb = (listToMaybe xs)
                     case mb of
                        Just res -> return (Just res)
                        _        -> return Nothing

lookupConstraints :: [IdStr] -> KTR Constraint
lookupConstraints ids = do cenv <- ktrGet conEnv
                           let cons = extractCons cenv ids
                           return cons

extendKEnv :: Id -> Kind -> KTR ()
extendKEnv id k = ktrUpdate (kEnv' (extendEnv id k))

extendBEnv :: Id -> Kind -> KTR ()
extendBEnv id k = ktrUpdate (bEnv' (extendEnv id k))

extendPEnv :: Id -> Kind -> KTR ()
extendPEnv id k = ktrUpdate (polys' (extendEnv id k))

extendConEnv :: Id -> Constraint -> KTR ()
extendConEnv id con = ktrUpdate (conEnv' (extendCEnv id con))

extendConUniv :: Constraint -> KTR ()
extendConUniv c = ktrUpdate (conUniv' (c /\))

extendInfG :: InfGoal -> KTR ()
extendInfG goal = ktrUpdate (infG' (goal:))

extendGraphV :: Vertex -> KTR ()
extendGraphV v = ktrUpdate (dGraph' (extendVertex v))

extendGraphE :: Edge -> KTR ()
extendGraphE e = ktrUpdate (dGraph' (extendEdge e))

--extendSK :: Constraint -> KTR ()
--extendSK cons = ktrUpdate (skTest' (cons /\))

--------------------------------------------------
-- Generating Constructor Environment
--------------------------------------------------

ktrGenEnvFromDT :: AST.DataType -> SrcInfo -> KTR ()
ktrGenEnvFromDT (AST.DataType id ts) src = do 
            hasBeenDec <- lookupCons (idStr id)
            kVar  <- newKindVar
            kVars <- newKindVars (length ts)
            let consKind = makePKind kVars
            let src2 = idSrcInfo id
            let cons = toConstraint ((kVar =+= consKind) (J [(srcLoc src),(srcLoc src2)]))
            --extendKEnv id kVar
            extendConUniv cons
            case hasBeenDec of
              Nothing -> extendKEnv id kVar
              Just _  -> doNothing
            --Just _  -> fail ("Error: Repeated definition of " ++ (idStr id))

ktrGenEnvFromCL :: AST.Class -> SrcInfo -> KTR ()
ktrGenEnvFromCL (AST.Class _ p _ _) src = do 
            let (AST.Pred src2 id ts) = p
            hasBeenDec <- lookupCons (idStr id)
            --case hasBeenDec of
            kVar  <- newKindVar
            kVars <- newKindVars (length ts)
            let consKind = makePKind kVars
            let src3 = idSrcInfo id
            let cons = toConstraint ((kVar =+= consKind) (J [(srcLoc src),(srcLoc src2),(srcLoc src3)]))
            --extendKEnv id kVar
            extendConUniv cons
            case hasBeenDec of
              Nothing -> do puts ((idStr id) ++ " " ++ (pretty kVar))
                            extendKEnv id kVar
              Just _  -> doNothing
            --Just _  -> fail ("Error: Repeated definition of " ++ (idStr id))                                                

ktrGenEnvFromCS :: AST.Constr -> SrcInfo -> KTR ()
ktrGenEnvFromCS (AST.ConstrCls id t) src = do
            hasBeenDec <- lookupCons (idStr id)
            case hasBeenDec of
               Nothing -> do mb <- convertToKind t
                             case mb of
                               Just k -> do puts ((idStr id) ++ " " ++ (pretty k))
                                            extendKEnv id k
                               _      -> fail ("Error: Unidentified Kind in constraint declaration. ")
               Just _  -> fail ("Error: Repeated definition of " ++ (idStr id))
ktrGenEnvFromCS (AST.ConstrData id t) src = do
            hasBeenDec <- lookupCons (idStr id)
            case hasBeenDec of
               Nothing -> do mb <- convertToKind t
                             case mb of
                               Just k -> do puts ((idStr id) ++ " " ++ (pretty k))
                                            extendKEnv id k
                               _      -> fail ("Error: Unidentified Kind in constraint declaration. ")
               Just _  -> fail ("Error: Repeated definition of " ++ (idStr id))

ktrGenEnvInit :: AST.Dec -> KTR()
ktrGenEnvInit dec = case dec of
                      AST.ConsDec src cs -> ktrGenEnvFromCS cs src
                      _                  -> doNothing

ktrGenEnv :: AST.Dec -> KTR ()
ktrGenEnv dec = do buildGraphStart dec
                   case dec of
                      AST.DataDec src dt _ -> ktrGenEnvFromDT dt src
                      AST.ClassDec src cl  -> ktrGenEnvFromCL cl src
                      --AST.ConsDec  src cs  -> ktrGenEnvFromCS cs src
                      _                    -> doNothing

------------------------------------------------------------
-- Dependency Graph Construction Procedures
------------------------------------------------------------

-- Main interface to build a dependency sub-graph (tree) with respect to
-- a given declaration.
buildGraphStart :: AST.Dec -> KTR ()
buildGraphStart = buildGraph "Start" 

class GraphTraversal a where
   buildGraph :: Vertex -> a -> KTR ()

instance GraphTraversal a => GraphTraversal [a] where
   buildGraph v xs = mapM_ (buildGraph v) xs

instance GraphTraversal AST.Dec where
   buildGraph _ (AST.DataDec _ dt cons) = do let (AST.DataType id _) = dt
                                             extendGraphV (idStr id)
                                             buildGraph (idStr id) cons
   buildGraph _ (AST.ClassDec _ c)      = do let (AST.Class ctxt p _ m) = c
                                             let (AST.Pred _ id _)      = p
                                             extendGraphV (idStr id)
                                             buildGraph (idStr id) ctxt
                                             buildGraph (idStr id) m
   buildGraph _ _                       = doNothing

instance GraphTraversal AST.Ctxt where
   buildGraph v (AST.Ctxt ps) = buildGraph v ps

instance GraphTraversal AST.Pred where
   buildGraph v (AST.Pred _ id ts) = do let edge = (v,(idStr id))
                                        extendGraphE edge
                                        buildGraph v ts

instance GraphTraversal AST.Cnst where
   buildGraph v (AST.Cnst ps) = buildGraph v ps

instance GraphTraversal AST.Prim where
   buildGraph v (AST.PredPrim p)     = buildGraph v p
   buildGraph v (AST.EqPrim _ t1 t2) = do buildGraph v t1
                                          buildGraph v t2

instance GraphTraversal AST.Type where
   buildGraph v (AST.VarType _)       = doNothing
   buildGraph v (AST.ConType id)      = do mb <- lookupBuiltIn (idStr id)
                                           case mb of
                                              Nothing -> extendGraphE (v,(idStr id))
                                              _       -> doNothing   
   buildGraph v (AST.AppType _ t1 t2) = do buildGraph v t1
                                           buildGraph v t2

instance GraphTraversal AST.Method where
   buildGraph v (AST.Method _ tschm) = buildGraph v tschm

instance GraphTraversal AST.TSchm where
   buildGraph v (AST.TSchm ctxt t) = do buildGraph v ctxt
                                        buildGraph v t

instance GraphTraversal AST.Cons where
   buildGraph v (AST.Cons _ _ cnst dt) = do let (AST.DataType _ ts) = dt
                                            buildGraph v ts
                                            buildGraph v cnst

----------------------------------------------------
-- Constraint Generation Over Various Kinded Domains
----------------------------------------------------

-- Misc function to restrict arguments of data constructor to kind of *
dataDefault :: Loc -> [Kind] -> KTR Constraint
dataDefault loc []     = return trueConstraint
dataDefault loc [k]    = do let j = J [loc]
                            return (toConstraint ((k =+= starTCon) j))
dataDefault loc (k:ks) = do c  <- dataDefault loc [k]
                            cs <- dataDefault loc ks
                            return (c /\ (cs))

-- Dummy Kind Variable 
dummyKind = TVar (mkVar "Dummy")

-- Misc function to combine a list of (Constraint,Kind) tuples
combineTuples :: [(Constraint,Kind)] -> (Constraint,[Kind])
combineTuples ((c1,k):xs) = let (c2,ks) = combineTuples xs
                            in ((c1 /\ c2),(k:ks))
combineTuples _           = (trueConstraint,[]) 

-- Misc function to generate n-tuple kinds when needed
checkForNTuple :: Id -> Env -> KTR Env
checkForNTuple id env = do case (isTupleKind (idStr id)) of
                              True  -> do let idst  = (idStr id)
                                          let idst' = nub (idst)
                                          let size  = (length idst) - (length idst') + 2
                                          let mb    = lookupEnv idst env
                                          --puts (show mb)
                                          case mb of
                                             Nothing -> do --extendBEnv id (makeDKind size)
                                                           let env' = extendEnv id (makeDKind size) env
                                                           return env'
                                             _       -> do --puts ("\n"++(pretty k))
                                                           return env
                              False -> return env

-- Misc function to generate a list of existential variables from a localized program fragment 
class EnvSource a where
   buildEnv :: a -> Env -> KTR Env

instance EnvSource a => EnvSource [a] where
   buildEnv [] env      = return env
   buildEnv (x:xs) env  = do env'  <- buildEnv x env
                             env'' <- buildEnv xs env'
                             return env''

instance EnvSource AST.Type where 
   buildEnv (AST.VarType id) env      = do let mb = lookupEnv (idStr id) env
                                           case mb of
                                              Nothing -> do k <- newKindVar
                                                            let env' = extendEnv id k env
                                                            return env'
                                              Just _  -> return env  
   buildEnv (AST.ConType _) env       = return env
   buildEnv (AST.AppType _ t1 t2) env = do env'  <- buildEnv t1 env
                                           env'' <- buildEnv t2 env'
                                           return env''

instance EnvSource AST.Pred where
   buildEnv (AST.Pred _ _ ts) env = buildEnv ts env

instance EnvSource AST.Ctxt where
   buildEnv (AST.Ctxt ps) env = buildEnv ps env

instance EnvSource AST.Prim where
   buildEnv (AST.PredPrim p) env     = buildEnv p env
   buildEnv (AST.EqPrim _ t1 t2) env = do env'  <- buildEnv t1 env
                                          env'' <- buildEnv t2 env'
                                          return env''

instance EnvSource AST.Cnst where
   buildEnv (AST.Cnst ps) env = buildEnv ps env

instance EnvSource AST.TSchm where
   buildEnv (AST.TSchm ctxt t) env = do env'  <- buildEnv ctxt env
                                        env'' <- buildEnv t env'
                                        return env''

instance EnvSource AST.Method where
   buildEnv (AST.Method _ tschm) env = buildEnv tschm env

-- Constraint Generation procedures
class KindDomain a where
   consOn :: Env -> a -> KTR (Constraint,Kind)

-----------------------------------
-- Constraint Generation over types

instance KindDomain AST.Type where
   consOn env (AST.VarType id)        = do 
            k' <- newKindVar
            case (idStr id) of
               "a!" -> return (trueConstraint,k')
               _    -> do let mb = lookupEnv (idStr id) env
                          case mb of
                             Just (EnvRes srcId k) -> do let src  = idSrcInfo id
                                                         let src2 = idSrcInfo srcId
                                                         return (toConstraint ((k' =+= k)(J [(srcLoc src),(srcLoc src2)])),k')
                             _                     -> fail ("Error: Variable " ++ (idStr id) ++  " not in scope.")
   consOn env (AST.ConType id)        = do
            k' <- newKindVar
            case (idStr id) of
               "a!" -> return (trueConstraint,k')
               _    -> do env' <- checkForNTuple id env
                          let mb = lookupEnv (idStr id) env'
                          --puts ("\n" ++ (idStr id) ++ "\n" ++ (pretty env')++"\n")
                          case mb of
                             Just (EnvRes srcId k) -> do let src  = idSrcInfo id
                                                         let src2 = idSrcInfo srcId
                                                         return (toConstraint ((k' =+= k)(J [(srcLoc src),(srcLoc src2)])),k')
                             _                     -> fail ("Error: Constructor " ++ (idStr id) ++ " not in scope.")
   consOn env (AST.AppType src t1 t2) = do
            k3      <- newKindVar
            (c1,k1) <- consOn env t1
            (c2,k2) <- consOn env t2
            let k2Arrk3 = (TApp (TApp (TCon (mkFreeName "->"))  k2) k3)
            let c' = toConstraint ((k1 =+= k2Arrk3 )(J [srcLoc src]))
            return (c1 /\ c2 /\ c', k3)

-------------------------------------------------------------
-- Constraint Generation over Primitive Constraints (Context)

instance KindDomain AST.Pred where
   consOn env (AST.Pred src id ts) = do 
            let mb = lookupEnv (idStr id) env
            case mb of 
               Just (EnvRes srcId k) -> do k' <- newKindVar
                                           let src2    = idSrcInfo id
                                           let src3    = idSrcInfo srcId
                                           let c1      = toConstraint ((k =+= k')(J [(srcLoc src2),(srcLoc src3)])) 
                                           xs <- mapM (consOn env) ts
                                           let (c2,ks) = combineTuples xs
                                           let ks'     = makePKind ks
                                           let c3      = toConstraint ((k' =+= ks')(J [srcLoc src]))
                                           return (c1 /\ c2 /\ c3, k')
               _                     -> fail ("Error: Class " ++ (idStr id) ++ " not in scope.")

instance KindDomain AST.Prim where
   consOn env (AST.PredPrim p)       = consOn env p
   consOn env (AST.EqPrim src t1 t2) = do (c1,k1) <- consOn env t1
                                          (c2,k2) <- consOn env t2
                                          let c3 = toConstraint ((k1 =+= k2)(J [srcLoc src]))
                                          return (c1 /\ c2 /\ c3, dummyKind)

instance KindDomain AST.Cnst where
   consOn env (AST.Cnst ps) = do xs <- mapM (consOn env) ps
                                 let (c,ks) = combineTuples xs
                                 return (c, dummyKind)

instance KindDomain AST.Ctxt where
   consOn env (AST.Ctxt ps) = do xs <- mapM (consOn env) ps
                                 let (c,ks) = combineTuples xs
                                 return (c, dummyKind)

-----------------------------------------------
-- Constraint Generation over Type Schemes

instance KindDomain AST.TSchm where
   consOn env (AST.TSchm ctxt t) = do
            env'   <- buildEnv ctxt env
            env''  <- buildEnv t env'
            (c1,_) <- consOn env'' ctxt
            (c2,k) <- consOn env'' t
            let c3 = (toConstraint (k =:= starTCon))
            return (c1 /\ c2 /\ c3, dummyKind)

instance KindDomain AST.Method where
   consOn env (AST.Method _ tsc) = consOn env tsc

-----------------------------------------------
-- Constraint Generation over value expressions

instance KindDomain AST.Exp where
   consOn env (AST.AppExp src e1 e2)  = do (c1,_) <- consOn env e1
                                           (c2,_) <- consOn env e2
                                           return (c1 /\ c2, dummyKind)
   consOn env (AST.AbsExp src _ e)    = consOn env e
   consOn env (AST.LetExp src lets e) = do xs     <- mapM (consOn env) lets
                                           let (c1,_) = combineTuples xs
                                           (c2,_) <- consOn env e
                                           return (c1 /\ c2, dummyKind)
   consOn env (AST.CaseExp src exps m)= do xs <- mapM (consOn env) exps
                                           ys <- mapM (consOn env) m
                                           let (c1,_) = combineTuples xs
                                           let (c2,_) = combineTuples ys
                                           return (c1 /\ c2,dummyKind)
   consOn env _                       = return (trueConstraint, dummyKind)

instance KindDomain AST.LetBnd where
   consOn env (AST.LetBnd src _ e)            = consOn env e
   consOn env (AST.LetBndAnn src _ _ tschm e) = do (c1,_) <- consOn env tschm
                                                   (c2,_) <- consOn env e
                                                   return (c1 /\ c2, dummyKind)

instance KindDomain AST.Match where
   consOn env (AST.Match _ e) = consOn env e

-----------------------------------------------
-- Constraint Generation over Data Constructors

instance KindDomain AST.Cons where
   consOn env (AST.Cons src ids cnst dt) = do ks       <- newKindVars (length ids)
                                              -- Extending env with existential variables
                                              let env' = extendEnvL ids ks env
                                              let (AST.DataType id ats) = dt
                                              -- Generate Constraints from type expressions
                                              xs       <- mapM (consOn env') ats
                                              let (c1,ks') = combineTuples xs
                                              c2       <- dataDefault (srcLoc src) ks'
                                              -- Generate Constraints from context
                                              (c3,_)   <- consOn env' cnst
                                              return ((c1 /\ c2 /\ c3),dummyKind)

---------------------------------------------------
-- Constraint Generation Over Declarations

-- Misc function, returns compositions of datatypes
getDTComp (AST.DataType id dts) = (id,dts)

instance KindDomain AST.Dec where
   consOn env (AST.DataDec src dt cs) = do
           let (id,dts) = getDTComp dt
           k  <- newKindVar
           ks <- newKindVars (length dts)
           let mb = lookupEnv (idStr id) env
           case mb of
              Just (EnvRes srcId k') -> do let src2 = idSrcInfo id
                                           let src3 = idSrcInfo srcId
                                           -- Build env from data type declaration
                                           env' <- buildEnv dts env
                                           -- Generate Constraints from LHS
                                           let c    = toConstraint ((k' =+= k) (J [(srcLoc src2),(srcLoc src3)]))
                                           xs <- mapM (consOn env') dts
                                           let (c',ks') = combineTuples xs
                                           let ks'' = makePKind ks'
                                           let c''  = toConstraint ((k =+= ks'') (J [(srcLoc src),(srcLoc src2)]))
                                           -- Generate Constraints from RHS (Data Cons)
                                           ys <- mapM (consOn env') cs
                                           let (c''',_) = combineTuples ys
                                           -- Update new constraints to constraint universe
                                           let cDec  = c /\ c' /\ c'' /\ c'''
                                           let cDec' = appendJust cDec src
                                           --extendConUniv (cDec) -- Mod
                                           extendConEnv id cDec
                                           return (trueConstraint, k')
              _                      -> fail ("Bug: Type constructor not found.")

   consOn env (AST.ClassDec src c) = do
           let (AST.Class ctxt p _ ms) = c
           -- Build env of existential variables
           env'  <- buildEnv ctxt env
           env'' <- buildEnv p env'
           -- Generate Constraints
           (c1,_) <- consOn env'' ctxt
           (c2,_) <- consOn env'' p
           xs     <- mapM (consOn env'') ms
           let (c3,_) = combineTuples xs
           let cDec  = c1 /\ c2 /\ c3
           let cDec' = appendJust cDec src
           --extendConUniv (cDec) -- Mod
           let (AST.Pred _ id _) = p
           extendConEnv id cDec
           return (trueConstraint, dummyKind)

   consOn env (AST.InstDec src inst) = do
           let (AST.Inst ctxt p wh) = inst
           -- Build env of existential variables
           env'  <- buildEnv ctxt env
           env'' <- buildEnv p env'
           -- Generate Constraints
           (c1,_) <- consOn env'' ctxt
           (c2,_) <- consOn env'' p
           let cDec  = c1 /\ c2
           let cDec' = appendJust cDec src
           extendConUniv cDec
           return (trueConstraint, dummyKind)

   consOn env (AST.PrimDec src pr) = do
           let (AST.Prim id _ tschm) = pr
           (c,_) <- consOn env tschm
           let cDec  = appendJust c src 
           extendConUniv c
           return (trueConstraint, dummyKind)

   consOn env (AST.ValDec src letb) = do 
           (c,_) <- consOn env letb
           let cDec  = appendJust c src
           extendConUniv c
           return (trueConstraint, dummyKind)

   consOn env (AST.RuleDec src rule) = do
           case rule of
              AST.SimpRule ctxt cnst -> do env'   <- buildEnv ctxt env
                                           env''  <- buildEnv cnst env'
                                           (c1,_) <- consOn env'' ctxt
                                           (c2,_) <- consOn env'' cnst
                                           let cDec  = c1 /\ c2
                                           let cDec' = appendJust cDec src
                                           extendConUniv (cDec)
                                           return (trueConstraint, dummyKind)
              AST.PropRule ctxt cnst -> do env'   <- buildEnv ctxt env
                                           env''  <- buildEnv cnst env'
                                           (c1,_) <- consOn env'' ctxt
                                           (c2,_) <- consOn env'' cnst
                                           let cDec  = c1 /\ c2
                                           let cDec' = appendJust cDec src
                                           extendConUniv (cDec)
                                           return (trueConstraint, dummyKind)

   consOn env _ = do return (trueConstraint, dummyKind)

-------------------------------------------------------------
-- Kind Validation Top Level Interface
-- Implementation of kind validation processes that supports
-- multiple error messages. Also allows accounts for possible
-- extensions for more detailed error messages. 
-- Still currently work in progress (As of 15 May 2005)
-------------------------------------------------------------

-- Dummy id and var functions for unlabelled constraint satisfiability test.
dummyId = anonId "dummy"
dummyVar = mkVar "dummy"

-- Basic satisfiability test without kind inference. Takes in source information and a
-- constraint set cons, and returns an error if cons is unsatifiable.
kindSatSingle :: SrcTextData -> Constraint -> IO [Error]
kindSatSingle srcT cons = do let infGs = [InfGoal dummyId True [dummyVar] cons]
                             infRs <- (Inf.runInfGoals [] infGs)
                             case infRs of
                                    []                  -> return []
                                    [InfSuccess _ _ _]  -> return []
                                    [InfFailure id c] ->   do errmsg <- generateKindErrorMsg "" srcT (InfFailure id c)
                                                              return [errmsg]          
                                    _                   -> fail "Bug: Other Inference Failure types found in kindSat"

-- Function to initial kind checking, for local kind conflicts within each dependency groups. Returns a list of
-- errors, or an empty list if there are no errors. 
kindSat :: SrcTextData -> [[Vertex]] -> CEnv -> IO [Error]
kindSat srcT (dGrph:dGrphs) cenv = do let cons = extractCons cenv dGrph
                                      let infGs = [InfGoal dummyId True [dummyVar] cons]
                                      infRs <- (Inf.runInfGoals [] infGs)
                                      case infRs of
                                        []                  -> kindSat srcT dGrphs cenv
                                        [InfSuccess _ _ _]  -> kindSat srcT dGrphs cenv
                                        [InfFailure id c] ->   do errmsg  <- generateKindErrorMsg "" srcT (InfFailure id c)
                                                                  unsat   <- minUnsatSubset (cBCons cons)
                                                                  --putStr ((pretty unsat)++"\n")
                                                                  errmsgs <- kindSat srcT dGrphs cenv
                                                                  return (errmsg:errmsgs)          
                                        _                   -> fail "Bug: Other Inference Failure types found in kindSat"
kindSat _ [] _                   = return []

-- Satisfiability test with kind inference. Takes in source information, a constraint set cons
-- and an environment env, containing constructor id to kind variable mappings of constructors
-- in interest for inference. Either returns an environment of id to inferred kind mappings, or
-- an error if cons is unsatisfiable.
-- Other assumptions:
--     i.  cons contains all constraints generated from a dependency group dx, plus all constraints from
--         type annotation context.
--     ii. env constains all constructor ids of constructors in dependency group dx (nothing more, nothing
--         less)
kindInference :: SrcTextData -> Constraint -> Env -> IO (Either Env Error)
kindInference srcT cons env = do let infGs = [InfGoal dummyId True [dummyVar] cons]
                                 infRs <- (Inf.runInfGoals [] infGs)
                                 case infRs of
                                    []                  -> return (Left emptyEnv)
                                    [InfSuccess _ _ c]  -> do let (Env res) = env
                                                              let env' = extendInferenceEnv res (cBCons c) emptyEnv
                                                              return (Left env')
                                    [InfFailure id c] ->   do errmsg <- generateKindErrorMsg "" srcT (InfFailure id c)
                                                              unsat  <- minUnsatSubset (cBCons cons)
                                                              --putStr ((pretty unsat)++"\n")
                                                              return (Right errmsg)
                                    _                   -> fail "Bug: Other Inference Failure types found in kindInference"

-- This function builds a new constructor id to kind mapping, with respect to the list of bcons
-- extracted from a successful inference result. Seeks out each id's respective inferred kind
-- and builds a new environment.
extendInferenceEnv :: [EnvRes] -> [BCons] -> Env -> Env
extendInferenceEnv ((EnvRes id k):envress) bcons env = let mb = findInfMapping k bcons
                                                       in case mb of
                                                            Just k' -> let env' = extendEnv id k' env
                                                                       in extendInferenceEnv envress bcons env'
                                                            _       -> extendInferenceEnv envress bcons env
extendInferenceEnv [] _ env                          = env

-- Auxilliary function for extendInferenceEnv, used to find an inferred kind k' with the kind variable k,
-- by locating a builtin constraint (k = k') from a list of builtin constraints. 
findInfMapping :: Kind -> [BCons] -> Maybe Kind
findInfMapping k (b:bs) = let k' = eqLeft b
                          in case (varStr k) == (varStr k') of
                               True  -> Just (eqRight b)
                               False -> findInfMapping k bs
findInfMapping _ []     = Nothing

-- Main Interface to execute the kind validation process.
kindValidate :: SrcTextData -> [AST.Dec] -> Bool -> IO (String,[Error])
kindValidate srcT ds b = do 
        --putStr ((pretty ds)++"\n")
        outCome  <- runKTR (defaultKState b) (genKindConstraint ds)
        case outCome of
           Succ st -> do let kenv     = kEnv st
                         let cenv     = conEnv st 
                         let grph     = dGraph st
                         let ctxtCons = conUniv st
                         let depGs    = depGroups grph
                         ctxtErr  <- kindSatSingle srcT ctxtCons
                         depGErrs <- kindSat srcT depGs cenv
                         let localErrs = ctxtErr ++ depGErrs
                         case localErrs of
                            [] -> do let conuniv = (mergeAllCons cenv) /\ ctxtCons
                                     e <- kindInference srcT conuniv kenv
                                     case e of
                                       Right infErr -> return ("",[infErr])
                                       Left  infEnv -> do --putStr ((pretty infEnv)++"\n")
                                                          case b of
                                                            True  -> runGHCValidation srcT st infEnv
                                                            False -> return ("",[])
                            _  -> return ("",localErrs)
           Err e   -> fail e

genKindConstraint :: [AST.Dec] -> KTR KState
genKindConstraint ds = do speak "Kind Validation Initialiated."
                          speak (pretty ds)
                          mapM_ ktrGenEnvInit ds
                          mapM_ ktrGenEnv ds
                          kenv <- ktrGet kEnv
                          benv <- ktrGet bEnv
                          let env = unionEnvs kenv benv
                          --puts (pretty env)
                          mapM_ (consOn env) ds
                          --genInfGoals 
                          st <- ktrGet ident
                          return st

-- Main interface to initiate kind inference processes, from data structures gathered from the 
-- constraint generation procedures. Returns a tuple consisting of the inferred environment and
-- a list of errors. (if any)
-- Post Condition: Return environment is a complete inferred environment of all constructors in
-- the target program, if no Errors are found.
-- Arguments: srcT - Source text information
--            grph - Dependency Graph of target program
--            env  - constructor id to kind variable environment
--            cenv - constructor id to local constraint set environment
--            ctxtCons - Context constraint set, ie. constraints generated from type annotations
-- Note: Currently, this function is not in use because of its incompleteness in finding
--       principal kindings.
buildInferenceEnv :: SrcTextData -> [[Vertex]] -> Env -> CEnv -> Constraint -> IO (Env,[Error])
buildInferenceEnv srcT depGs env cenv ctxtCons = do 
         runInf depGs env cenv ctxtCons
         where
            runInf dGrps env' cenv' cons = do 
                  case dGrps of
                    []          -> return (emptyEnv,[])
                    dGrp:dGrps' -> do let grpEnv  = fetchEnv dGrp env'
                                      let grpCons = (fetchCons dGrp cenv') /\ cons
                                      (env'',errMsgs) <- runInf dGrps' env' cenv' cons
                                      e <- kindInference srcT grpCons grpEnv
                                      case e of
                                        Right errMsg -> return (env'',errMsg:errMsgs)
                                        Left  env''' -> return ((unionEnvs env'' env'''),errMsgs)
                                    
fetchEnv :: [Vertex] -> Env -> Env
fetchEnv (str:strs) env = case (lookupEnv str env) of
                            Just envres -> let env' = fetchEnv strs env
                                           in extendEnvInt env' envres
                            _           -> error "Bug: Problem in fetchEnv"
fetchEnv [] _           = emptyEnv 

fetchCons :: [Vertex] -> CEnv -> Constraint
fetchCons strs cenv = extractCons cenv strs 

-------------------------------------------
-- Mimic GHC Procedures
-------------------------------------------

-- Main interface that follows after standard kind validation. Receives src text data and the
-- state that follows after kind validation, and the principal kinding environment. This function 
-- executes GHC style kind inference and compares its results with the principal kindings. Returns
-- an error if GHC defaulting scheme varies from principal kindings.
runGHCValidation :: SrcTextData -> KState -> Env -> IO (String,[Error])
runGHCValidation srcT st infEnv = do 
                     outCome <- runKTR st (ghcKindInference)
                     case outCome of
                        Succ st' -> do infRes <- processInfGoals (infG st')
                                       env <- processResults infRes
                                       let verbMsg = ("GHC Kind Interpretation: " ++ (pretty env) ++ "\n")
                                       let dCons = defaultedConstraints env (kEnv st')
                                       let verbMsg' = verbMsg ++ ("Defaulted Constraints: " ++ (pretty dCons) ++ "\n")
                                       let conuniv = dCons /\ mergeAllCons (conEnv st') /\ (conUniv st')
                                       infRes' <- processInfGoals ([InfGoal dummyId True [dummyVar] conuniv])
                                       case (hasFailure infRes') of
                                          True  -> do let msg = checkDefaulting infEnv env
                                                      --putStr (msg)
                                                      --putStr (pretty env)
                                                      errList <- checkResults msg srcT infRes'
                                                      return (verbMsg',errList)
                                          False -> return (verbMsg',[])
                        _        -> fail "Bug: Problem in runGHCValidation"

ghcKindInference :: KTR KState
ghcKindInference = do cenv <- ktrGet conEnv
                      let ids = getCEnvIds cenv
                      mapM_ ghcInfGoals ids
                      st <- ktrGet ident
                      return st

-- Generate inference goal from a given constructor id. Constraint set to be inferred from, is
-- determined by the constructor dependency graph. This is identical with GHC kind inference.
ghcInfGoals :: Id -> KTR ()
ghcInfGoals id = do dGr <- ktrGet dGraph
                    let deps = tClosure dGr (idStr id)
                    cons <- lookupConstraints deps
                    mb   <- lookupCons (idStr id)
                    case mb of
                       Just (EnvRes _ k)-> case k of
                                              TVar v -> extendInfG (InfGoal id True [v] cons)
                                              _      -> fail ("Bug: Kind found in ghcInfGoals is not variable")
                       _             -> fail ("Bug: Missing kind variables in ghcInfGoals")                  

processInfGoals :: [InfGoal] -> IO [InfResult]
processInfGoals infGs = (Inf.runInfGoals [] infGs)

-- Simple Boolean check function. Determines if a list of InfResult contains any inference failures.                           
hasFailure :: [InfResult] -> Bool
hasFailure (infR:infRs) = case infR of
                             InfSuccess _ _ _ -> hasFailure infRs
                             InfFailure _ _ -> True
hasFailure []           = False

-- Function used to process a list of InfResults into a list of errors. Returns an empty list if
-- all InfResults in the list are successes (InfSuccess)
checkResults :: String -> SrcTextData -> [InfResult] -> IO [Error]
checkResults isDefault srcT (ir:irs) = do 
        case ir of
           InfSuccess _ _ _   -> checkResults isDefault srcT irs
           InfFailure id c    -> do --putStr ("Kind Error Detected.\n")
                                    errmsg <- generateKindErrorMsg isDefault srcT (InfFailure id c)  
                                    return [errmsg]
checkResults _ _ []          = return []                         

findKind :: Kind -> [BCons] -> Kind
findKind k (b:bs) = let k' = eqLeft b
                    in case (varStr k) == (varStr k') of
                         True  -> eqRight b
                         False -> findKind k bs
findKind _ _      = error ("Can't find kind to infer")

varStr k = varNameStr (fromTVar k)  

processResults :: [InfResult] -> IO Env
processResults (ir:irs) = do env <- processResults irs
                             case ir of
                                InfSuccess id [k] _ -> return (extendEnv id (defaultKind k) env)
                                _                   -> error ("Bug: processResults")
processResults []       = return (Env [])

defaultKind :: Kind -> Kind
defaultKind (TVar _)     = starTCon
defaultKind (TCon nm)    = TCon nm
defaultKind (TApp t1 t2) = TApp (defaultKind t1) (defaultKind t2)

-- Main function that runs all default error checking procedures, receives 2 environments ENV,
-- assumed to be the principal kinding environment and GHC style inferred environment.
defaultedConstraints :: Env -> Env -> Constraint
defaultedConstraints env1 env2 = let ids = getEnvIds env1
                                 in defaultedConstraintsInt ids env1 env2

defaultedConstraintsInt :: [Id] -> Env -> Env -> Constraint
defaultedConstraintsInt (id:ids) env1 env2 = 
        case (lookupEnv (idStr id) env1) of
           Just (EnvRes id1 k) -> case (lookupEnv (idStr id) env2) of
                                    Just (EnvRes id2 k') -> let src1 = idSrcInfo id1
                                                                src2 = idSrcInfo id2
                                                            in let cons = toConstraint ((k =+= k')(J [(srcLoc src1),(srcLoc src2)]))
                                                               in cons /\ (defaultedConstraintsInt ids env1 env2)
                                    _                    -> error "Bug: Problem in defaultConstraints"
           _                   -> error "Bug: Problem in defaultConstraints"
defaultedConstraintsInt [] _ _             = trueConstraint

-- Main function that runs all default error checking procedures, receives 2 environments ENV,
-- assumed to be the principal kinding environment and GHC style inferred environment.
checkDefaulting :: Env -> Env -> String
checkDefaulting env1 env2 = let ids = getEnvIds env1
                            in checkDefaultingInt ids env1 env2

checkDefaultingInt :: [Id] -> Env -> Env -> String
checkDefaultingInt (id:ids) env1 env2 =
         case (lookupEnv (idStr id) env1) of
           Just (EnvRes id1 k) -> case (lookupEnv (idStr id) env2) of
                                    Just (EnvRes id2 k')  -> case (hasDefaultError k k') of
                                                                True  -> (mkDefaultErrMsg id k k')++(checkDefaultingInt ids env1 env2)
                                                                False -> checkDefaultingInt ids env1 env2  
                                    _                     -> error "Bug: Problem in checkDefaulting"
           _                   -> error "Bug: Problem in checkDefaulting"
checkDefaultingInt [] _ _ = ""

mkDefaultErrMsg :: Id -> Kind -> Kind -> String
mkDefaultErrMsg id k k' = "Kind Annotation Required in: " ++ (idStr id) ++ "\n" ++
                          "    Required  Kind: " ++ (pretty k) ++ "\n" ++
                          "    Defaulted Kind: " ++ (pretty k') ++ "\n"

-- Simple checking procedure to check for GHC default errors
-- Compares 2 Kinds, assumed to be the principal kind and GHC 
-- style inferred kind respectively.                      
hasDefaultError :: Kind -> Kind -> Bool
hasDefaultError (TApp _ _) (TCon _)         = True
hasDefaultError (TApp t1 t2) (TApp t1' t2') = or [(hasDefaultError t1 t1'),(hasDefaultError t2 t2')]
hasDefaultError _ _                         = False

------------------------------------------------------------
-- Graph Data Type
-- These procedures implements a simple graph data structure
-- and an O(n(m+n)) where n=nodes,m=edges algorithm that
-- computes the transitive closure of dependencies between
-- type constructor and type class definitions. With these
-- information, we can construct the dependency groups, as
-- described in the haskell 98 report, for GHC style kind
-- inference.
------------------------------------------------------------

type Vertex = String
type Edge = (Vertex,Vertex)
data Graph = Graph [Vertex] [Edge]

emptyGraph = Graph [] []

extendVertex :: Vertex -> Graph -> Graph
extendVertex v (Graph vs es) = Graph (v:vs) es

extendEdge :: Edge -> Graph -> Graph
extendEdge e (Graph vs es) = Graph vs (e:es)

edgeSource :: Edge -> Vertex
edgeSource (v1,v2) = v1

edgeDestin :: Edge -> Vertex
edgeDestin (v1,v2) = v2

removeFrom :: [Vertex] -> [Vertex] -> [Vertex]
removeFrom (x:xs) his = case (elem x his) of
                           True  -> removeFrom xs his
                           False -> x:(removeFrom xs his)
removeFrom [] his = []

tClosureInt :: [Vertex] -> Graph -> Vertex -> [Vertex]
tClosureInt his (Graph vs es) v = let reqEdges = filter ((==v) . edgeSource) es
                                  in let children = map edgeDestin reqEdges
                                     in let children' = removeFrom children (v:his)
                                        in nub (v:(concatMap (tClosureInt (v:his) (Graph vs es)) children'))

-- function to find transitive closure of vertice v from a graph
tClosure :: Graph -> Vertex -> [Vertex]
tClosure (Graph vs es) v = case (elem v vs) of
                             True  -> tClosureInt [] (Graph vs es) v
                             False -> []

-- function to force a directed graph to an undirected graph, by naively making it symmetric
symmetric :: Graph -> Graph
symmetric (Graph vs es) = Graph vs (nub (reverseIt es))
                          where reverseIt ls = case ls of
                                                 []       -> []
                                                 (a,b):ts -> (a,b):(b,a):(reverseIt ts)

-- function to find a list of dependency groups (connected components) from a given graph
depGroups :: Graph -> [[Vertex]]
depGroups (Graph vs es) = nub (depGroupsInt vs (symmetric (Graph vs es)))
                          where depGroupsInt (v':vs') g = 
                                   let clo = sort (tClosure g v')
                                   in case vs' of 
                                        [] -> clo:[]
                                        _  -> clo:(depGroupsInt vs' g)
                                depGroupsInt [] _ = []  

instance Pretty Graph where
   pretty (Graph vs es) = "Vertice: " ++ (show vs) ++ "Edges: " ++ (show es)

----------------------------------------
-- Test Procedure For Sub Kind Extension 
----------------------------------------

{-

mkSKUC :: Kind -> Kind -> UCons
mkSKUC k1 k2 = njUC (mkFreeName "SubKind") [k1,k2]

-- SubKind a a <==> True
reflexRule = SimpRule CHRInfo [mkSKUC (TVar (mkVar "a")) (TVar (mkVar "a"))] trueConstraint

-- SubKind (a->b) (c->d) <==> SubKind a c, SubKind d b
coVariRule = let app1  = TApp (TApp (TCon (mkFreeName "->")) (TVar (mkVar "a"))) (TVar (mkVar "b"))
                 app2  = TApp (TApp (TCon (mkFreeName "->")) (TVar (mkVar "c"))) (TVar (mkVar "d"))
                 cons1 = toConstraint (mkSKUC (TVar (mkVar "a")) (TVar (mkVar "c")))
                 cons2 = toConstraint (mkSKUC (TVar (mkVar "d")) (TVar (mkVar "b")))
             in SimpRule CHRInfo [mkSKUC app1 app2] (cons1 /\ cons2)  

-- SubKind a b, SubKind b c ==> SubKind a c
transiRule = let uc1  = mkSKUC (TVar (mkVar "a")) (TVar (mkVar "b"))
                 uc2  = mkSKUC (TVar (mkVar "b")) (TVar (mkVar "c"))
                 cons = toConstraint (mkSKUC (TVar (mkVar "a")) (TVar (mkVar "c")))
             in PropRule CHRInfo [uc1,uc2] cons

-- SubKind Nat * <==> True
specialRule = SimpRule CHRInfo [mkSKUC (TCon (mkFreeName "Nat")) (TCon (mkFreeName "*"))] trueConstraint

skCHRs = [reflexRule,coVariRule,transiRule,specialRule]

modConsOn :: Env -> AST.Type -> KTR (Constraint,Kind)
modConsOn env (AST.VarType id)        = do
            k' <- newKindVar
            let mb = lookupEnv (idStr id) env
            case mb of
               Just (EnvRes srcId k) -> do let src  = idSrcInfo id
                                           let src2 = idSrcInfo srcId
                                           return (toConstraint ((k =+= k')(J [(srcLoc src),(srcLoc src2)])),k')
               _                     -> fail ("Error: Variable " ++ (idStr id) ++  " not in scope.")
modConsOn env (AST.ConType id)        = do
            k' <- newKindVar
            case (idStr id) of
               "intT1!" -> return (trueConstraint,k')
               _        -> do env' <- checkForNTuple id env
                              let mb = lookupEnv (idStr id) env'
                              case mb of
                                Just (EnvRes srcId k) -> do let src  = idSrcInfo id        
                                                            let src2 = idSrcInfo srcId       
                                                            return (toConstraint ((k =+= k')(J [(srcLoc src),(srcLoc src2)])),k')
                                _                     -> fail ("Error: Constructor " ++ (idStr id) ++ " not in scope.")
modConsOn env (AST.AppType src t1 t2) = do
            k3      <- newKindVar
            k4      <- newKindVar
            (c1,k1) <- modConsOn env t1
            (c2,k2) <- modConsOn env t2                                   
            let k3Arrk4 = (TApp (TApp (TCon (mkFreeName "->"))  k3) k4)
            let c3 = toConstraint ((k1 =+= k3Arrk4 )(J [srcLoc src]))
            let c4 = toConstraint (mkSKUC k2 k3)
            return (c1 /\ c2 /\ c3 /\ c4, k4)

processSK :: Constraint -> IO ()
processSK cons = do let infGs = [InfGoal dummyId True [dummyVar] cons] 
                    infR <- (Inf.runInfGoals skCHRs infGs)
                    case infR of
                      []                 -> putStr "Crap1"
                      [InfSuccess _ _ c] -> putStr ((pretty c) ++ "\n")
                      _                  -> putStr "Crap2"

natKind  = TCon (mkFreeName "Nat")
starKind = TCon (mkFreeName "*")

testCons :: Constraint
testCons = let var6 = TVar (mkVar "k6")
               var7 = TVar (mkVar "k7")
               var8 = TVar (mkVar "k8")
               app1 = makePKind [natKind,natKind,natKind]
           in let con1 = toConstraint ( ((TVar (mkVar "k6")) =+= (TCon (mkFreeName "*"))) (J [6]) )
                  con2 = toConstraint ( ((TVar (mkVar "k7")) =+= (TCon (mkFreeName "Nat"))) (J [7]) )
                  con3 = toConstraint ( ((TVar (mkVar "k8")) =+= (TCon (mkFreeName "Nat"))) (J [8]) )
                  con4 = toConstraint ( ((TVar (mkVar "k'")) =+= (makePKind [var6,var7,var8])) (J [9]) )
                  con5 = toConstraint ( ((TVar (mkVar "k5")) =+= app1) (J [5]) )
                  con6 = toConstraint ( UC (mkFreeName "SubKind") [(TVar (mkVar "k'")),(TVar (mkVar "k5"))] (J [9]) )
              in con1 /\ con2 /\ con3 /\ con4 /\ con5 /\ con6               

-}

--------------------------------------
-- CHR stuff no longer in use
-- Kept for historic purposes...
--------------------------------------

{-
-- CHRs for Builtin Type Constructors

nullCHR :: String -> CHR
nullCHR str = let x  = TVar (mkVar "x")
                  uc = njUC (mkFreeName (str)) [x]
              in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind 0)))

listCHR = let x  = TVar (mkVar "x")
              uc = njUC (mkFreeName (listCons)) [x]
          in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind 1)))

funcCHR = let x  = TVar (mkVar "x")
              uc = njUC (mkFreeName (funcCons)) [x]
          in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind 2)))

emptCHR = let x  = TVar (mkVar "x")
              uc = njUC (mkFreeName (emptCons)) [x]
          in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind 0)))

tupleCHR n = let x  = TVar (mkVar "x")
                 uc = njUC (mkFreeName ((tupleCons n))) [x]
             in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind n)))

numCHR = let x  = TVar (mkVar "x")
             uc = njUC (mkFreeName (numClass)) [x]
         in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind 1)))

fracCHR = let x  = TVar (mkVar "x")
              uc = njUC (mkFreeName (fracClass)) [x]
          in SimpRule CHRInfo [uc] (toConstraint (x =:= (makeDKind 1)))

-- Make Initial CHRs (Pre-Inference)
-- makePredCHR id k [k1 ... kn] = id k <==> (k = k1 -> ... -> kn)
makePredCHR :: Id -> Kind -> [Kind] -> CHR
makePredCHR id kVar kVars = let uc   = njUC (mkName (idStr id) (idSrcInfo id) (idStr id)) [kVar]
                                pLoc = srcLoc (idSrcInfo id) 
                            in SimpRule CHRInfo [uc] (toConstraint ((kVar =+= (makePKind kVars)) pLoc) )

-- Make Inferred CHRs from the inferred kinds
-- makeInfCHR id k = id x <==> (x = k) 
makeInfCHR :: Id -> Kind -> CHR
makeInfCHR id k = let x    = TVar (mkVar "x")
                      uc   = njUC (mkName (idStr id) (idSrcInfo id) (idStr id)) [x]
                      pLoc = srcLoc (idSrcInfo id)
                  in SimpRule CHRInfo [uc] (toConstraint ((x =+= k) pLoc))

-}

{-

---------------------------------------------------
-- Previous kind validation implementation

-- Misc function, generate Inference Goals
genInfGoals :: KTR ()
genInfGoals = do (Env res) <- ktrGet kEnv
                 --puts ("Res: " ++ show res)
                 cUniv   <- ktrGet conUniv
                 case res of
                   [] -> doNothing
                   _  -> do let infG = makeInfGoal cUniv (head res)
                            extendInfG infG  
                            --let infGs = map (makeInfGoal cUniv) res
                            --mapM_ extendInfG infGs


makeInfGoal :: Constraint -> EnvRes -> InfGoal
makeInfGoal cUniv (EnvRes id kind) = 
          case kind of
             TVar v -> InfGoal id True [v] cUniv
             _      -> error ("Bug: In makeInfGoal, non-TVar Type found!!") 

-- Main kind validation interface. Receives source text information (SrcTextData) of preparing
-- error message, a list of declarations for kind inference/checking and a boolean that states
-- if user has choosen the mimic GHC option. Function returns a tuple which contains a string
-- which contains information for verbosity printing, and a list of kind errors (if any)
kindValidate :: SrcTextData -> [AST.Dec] -> Bool -> IO (String,[Error])
kindValidate srcT ds b = do 
        outCome  <- runKTR (defaultKState b) (kindInference ds)
        case outCome of
           Succ st -> do infRes  <- processInfGoals (infG st)
                         --processSK (skTest st)
                         errList <- checkResults [] srcT infRes
                         case errList of
                            [] -> do env <- processGlobalResults infRes (kEnv st)
                                     let infKState = prepState env st
                                     let verbMsg = "Inferred Kinds: " ++ (pretty env) ++ "\n"
                                     case b of
                                        True  -> do --outCome' <- runKTR infKState (reportKindInfRes)
                                                    --putStr ("Inferred Kinds: " ++ (pretty env) ++ "\n")
                                                    (verbMsg',errs) <- runGHCValidation srcT infKState
                                                    return (verbMsg++verbMsg',errs)
                                        False -> do --outCome' <- runKTR infKState (reportKindInfRes)
                                                    --putStr ("Inferred Kinds: " ++ (pretty env) ++ "\n")
                                                    return (verbMsg,[])
                            _  -> return ("",errList)
           Err e   -> fail e

test1 ds = do speak "Kind Validation Initialiated."
              speak (pretty ds)
              mapM_ ktrGenEnv ds
              kenv <- ktrGet kEnv
              benv <- ktrGet bEnv
              let env = unionEnvs kenv benv
              mapM_ (consOn env) ds 
              st <- getState
              speak st

reportKindInfRes :: KTR ()
reportKindInfRes = do kenv <- ktrGet kEnv
                      speak ("Inferred Kinds: " ++ (pretty kenv))
                      speak ("Kind Validation Concluded.")

-- Main function that initialises the kind inference engine. This function
-- represents the heart of the kind inference process of the "liberal"
-- inference scheme, that implements the validation of kinds with respect
-- to the principal kindings of a program.
kindInference :: [AST.Dec] -> KTR KState
kindInference ds = do speak "Kind Validation Initialiated."
                      speak (pretty ds)
                      mapM_ ktrGenEnv ds
                      kenv <- ktrGet kEnv
                      benv <- ktrGet bEnv
                      let env = unionEnvs kenv benv
                      mapM_ (consOn env) ds
                      genInfGoals 
                      --st <- getState
                      --speak st
                      st <- ktrGet ident
                      return st

processGlobalResults :: [InfResult] -> Env -> IO Env
processGlobalResults [infR] env = do 
          case infR of
             InfSuccess _ _ c -> do let (Env res) = env
                                    let env' = extendGlobalKindEnv res (cBCons c) emptyEnv
                                    return env'                                    
             _                -> fail "Bug: Problem in processGlobalResults"
 
processGlobalResults [] env     = return env 

processGlobalResults _ _        = fail "Bug: Problem in processGlobalResults"

extendGlobalKindEnv :: [EnvRes] -> [BCons] -> Env -> Env
extendGlobalKindEnv ((EnvRes id k):envress) bcons env = let k' = findKind k bcons
                                                        in let env' = extendEnv id k' env
                                                           in extendGlobalKindEnv envress bcons env'
extendGlobalKindEnv [] _ env                          = env

-}

