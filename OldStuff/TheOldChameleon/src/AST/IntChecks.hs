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
-- | This module provides static checks of the AST data structure for 
-- Chameleon's internal language. See doc\internal_AST.txt for details.
--
-- We perform the following checks
--
-- * non-overloaded values are only declared once
--
-- * patterns are linear
--
--------------------------------------------------------------------------------
module AST.IntChecks (
    internalASTChecks
)
where

import Monad
import List

import Misc
import Misc.ErrorMsg
import AST.SrcInfo
import AST.Internal

import TypeError.ErrorMsg
import Misc.Print
import Misc.Pretty
--import qualified Misc.Output.ANSI as ANSI

--------------------------------------------------------------------------------

-- | Performs all internal checks.
internalASTChecks :: [Id] -> [Id] -> [Dec] -> Prog -> SrcTextData -> IO ()
internalASTChecks imptTypes imptVals imptDecs p srcT = do
    let (Prog ms) = p
    let decs = concatMap moduleDecs ms
    --putStr ("DataCons:"++(show (findDataCons decs))++"\n"++(pretty decs)++"\n")
    let primEnv           = (constructEnv (decs++imptDecs)) ++
                            [":","enum","Chameleon.Primitive.patternMatchFailed"] ++ 
                            ["Chameleon.Primitive.fromInteger","+","-","/","*"] ++
                            ["Chameleon.Primitive.undefined"]
        imptVals'         = filterMethods imptDecs imptVals
        (conEnv1,datEnv1) = (constructConsEnv (decs++imptDecs))
        conEnv2           = ["Int","Bool","Integer","Float","Char","Double","[]","->"]
        datEnv2           = [":","()","True","False","[]","(,)"] 
        methEnv           = constructMethEnv (decs++imptDecs)
    --putStr ("\n After Filtering: " ++ (pretty imptVals') ++ "\n")
    let vsConSites              = varNotInScopeCheck (primEnv++(idToStr imptVals')) decs
        (_,nlpConSites)         = patternVarCheck [] decs
        (env1,env2,dupConSites) = dupConsCheck ([],[]) decs
        missConSites            = missingConsCheck (conEnv1++conEnv2++(idToStr imptTypes),datEnv1++datEnv2++(idToStr imptVals')) decs
        missMethSites           = missingMethodCheck methEnv decs
        (env3,dupMethSites1)    = dupMethodCheck True [] decs
        (_,dupMethSites2)       = dupMethodCheck False env3 decs
        -- other checks go here
    let conSites = vsConSites ++ nlpConSites ++ dupConSites ++ missConSites ++
                   missMethSites ++ dupMethSites1 ++ dupMethSites2
        msgs   = processConflictSites srcT (filterAnonSrcs conSites)
        endmsg = "" -- totalCSMsg conSites
    case null conSites of
      True  -> return ()
      False -> exit (msgs++endmsg)

filterMethods :: [Dec] -> [Id] -> [Id]
filterMethods classDecs ids =
      let methodIds = extractMeth classDecs
      in removeIntersects ids methodIds
      where
         extractMeth (dec:decs) = 
             let meths = extractMeth decs
             in case dec of
                  (ClassDec _ cls) -> let (Class _ _ _ mts) = cls
                                      in getIds mts
                                      where 
                                        getIds ((Method id _):mts) =
                                             id:(getIds mts)
                                        getIds [] = []
                  _                -> bug "Bug in filterMethods"
         extractMeth [] = []
         removeIntersects (id:ids) meths =
             case (idStr id) `elem` (idToStr meths) of
               True  -> removeIntersects ids meths
               False -> id:(removeIntersects ids meths)
         removeIntersects [] _ = []
  
filterAnonSrcs :: [ConflictSites] -> [ConflictSites]
filterAnonSrcs (cs:css) = case cs of
                            (CS _ [src]) -> case (srcLoc src) of
                                              -1  -> filterAnonSrcs css
                                              _   -> cs:(filterAnonSrcs css)
                            _            -> cs:(filterAnonSrcs css)
filterAnonSrcs []       = []

--------------------------------------------------------------------------------

{-

-- Checks that all pattern matches are linear.
-- Returns a list of the source locations of repeated variables.
checkNonLinearPats :: Prog -> [(SrcInfo,SrcInfo)]
checkNonLinearPats (Prog ms) = let ds = concatMap moduleDecs ms 
			       in  ckDecs ds
  where
    ckDecs ds = 
	let lbs = [ lb | (ValDec _ lb) <- ds ]
	in  concatMap ckLetBnd lbs

    ckLetBnd :: LetBnd -> [(SrcInfo,SrcInfo)]
    ckLetBnd lb = ckExp $ case lb of LetBnd _ _ e -> e
				     LetBndAnn _ _ _ _ e -> e

    ckExp :: Exp -> [(SrcInfo,SrcInfo)]
    ckExp exp = case exp of
	AppExp _ e1 e2  -> ckExp e1 ++ ckExp e2
	AbsExp _ _ e    -> ckExp e
	LetExp _ lbs e  -> ckExp e ++ concatMap ckLetBnd lbs
	CaseExp s es ms -> concatMap ckExp es ++ concatMap ckMatch ms 
	_ -> []

    ckMatch (Match ps e) = ckExp e ++ snd (ckPats [] ps)
    
    ckPats :: [Id] -> [Pat] -> ([Id], [(SrcInfo,SrcInfo)])
    ckPats vs []     = (vs, [])
    ckPats vs (p:ps) = let (vs1,s)  = ckPat  vs  p
			   (vs2,ss) = ckPats vs1 ps
		       in  (vs2, s ++ ss)

    ckPat :: [Id] -> Pat -> ([Id], [(SrcInfo,SrcInfo)])
    ckPat vs (ConPat _ _ ps) = ckPats vs ps
    ckPat vs (LitPat _) = (vs, [])
    ckPat vs (VarPat id) | v `elem` (idToStr vs) && not anon = (vs, [srcInfoPair id vs])
			 | otherwise	              	     = (id:vs, [])
      where
	v    = idStr id
	anon = case v of ('_':_) -> True
			 _ -> False
        idToStr (id:ids) = (idStr id):(idToStr ids)
        idToStr []       = [] 
        srcInfoPair id (v:vs) = let idstr1 = idStr id
                                    idstr2 = idStr v  
                                in case (idstr1==idstr2) of
                                      True  -> ((getSrcInfo id),(getSrcInfo v))
                                      False -> srcInfoPair id vs
        srcInfoPair _ []      = bug "Problem in ckPat, srcInfoPair"

reportNonLinearPats :: SrcTextData -> (SrcInfo,SrcInfo) -> String
reportNonLinearPats srcT (s1,s2) = 
       errorMsg s1 [msg++hl]
       where msg = "repeated pattern variable:\n" ++
                   "conflicting sites:\n"
             hl = generateSelectiveHL srcT [(srcLoc s1),(srcLoc s2)]
                                  
-}        
--------------------------------------------------------------------------------

checkRedeclaredValues :: Prog -> [SrcInfo]
checkRedeclaredValues (Prog ds) = bug "checkRedeclaredValues not implemented"

--------------------------------------------------------------------------------

-- Data Structure containing a flag indicating the type of syntax error, and a list
-- of locations contributing to the error.

data ConflictSites = CS Char [SrcInfo] | Empt deriving (Show)

data TCMethods = TCM Id [Id] | Meth [Id] deriving (Show)

mergeMethodEnv :: [TCMethods] -> [TCMethods] -> [TCMethods]
mergeMethodEnv (x:xs) ys = let ys' = mergeMethodEnvInt x ys True
                           in mergeMethodEnv xs ys'
mergeMethodEnv [] ys     = ys

mergeMethodEnvInt :: TCMethods -> [TCMethods] -> Bool -> [TCMethods]
mergeMethodEnvInt tcm1@(TCM tcId1 mIds1) ((TCM tcId2 mIds2):tcms) x = 
        case (idStr tcId1) == (idStr tcId2) of
          True  -> mergeMethodEnvInt tcm1 tcms False
          False -> (TCM tcId2 mIds2):(mergeMethodEnvInt tcm1 tcms x)
mergeMethodEnvInt (Meth ids1) ((Meth ids2):meths) _ = --mergeMethodEnvInt (Meth (ids1++ids2)) meths True
        let ids' = combineMeth ids1 ids2
        in mergeMethodEnvInt (Meth ids') meths True
        where
           combineMeth ids1 (id:ids2) = case (idStr id) `elem` (idToStr ids1) of
                                          True  -> combineMeth ids1 ids2
                                          False -> combineMeth (id:ids1) ids2
           combineMeth ids []         = ids 

mergeMethodEnvInt tcm [] True  = [tcm]
mergeMethodEnvInt tcm [] False = []
mergeMethodEnvInt _ _ _        = bug "Some crazy bug in mergeMethodEnvInt"

data IntEnv = IntEnv { ident  :: IdStr,
                       hlSrcs :: [SrcInfo]
              }

intEnvToStr :: [IntEnv] -> [IdStr]
intEnvToStr (x:xs) = (ident x):(intEnvToStr xs)
intEnvToStr []     = []

extendHLSrcs :: [SrcInfo] -> [IntEnv] -> [IntEnv]
extendHLSrcs srcs1 ((IntEnv str srcs2):intenvs) = (IntEnv str (srcs1++srcs2)):(extendHLSrcs srcs1 intenvs)
extendHLSrcs _ []                               = []

getHLSrcs :: IdStr -> [IntEnv] -> [SrcInfo]
getHLSrcs str1 ((IntEnv str2 srcs):intenvs) = 
         case str1 == str2 of
           True  -> srcs
           False -> getHLSrcs str1 intenvs
getHLSrcs _ [] = []

-- Simple utility function for error message printing for various
-- internal AST errors.

intErrorMsg :: Char -> String
intErrorMsg v = case v of
                  '1'  -> "Type variable not in scope"
                  '2'  -> "Repeated pattern variable"
                  '3'  -> "Variable not in scope"
                  '4'  -> "Duplicate data constructor declaration"
                  '5'  -> "Duplicate type constructor declaration"
                  '6'  -> "Duplicate type class declaraton"
                  '7'  -> "Duplicate type annotation"
                  '8'  -> "Unknown type constructor"
                  '9'  -> "Unknown type class"
                  '0'  -> "Unknown data constructor"
                  'A'  -> "Missing method definitions in class instance"
                  'B'  -> "Method definitions not in scope"
                  'C'  -> "Duplicate method declaration"
                  _    -> "Bug: Generic unknown error"

-- Error message interface to TypeError/ErrorMsg.hs methods. 

reportIntCheckError :: SrcTextData -> String -> [SrcInfo] -> String
reportIntCheckError srcT msg (s1:ss) = 
       errorMsg s1 [msg++"\n"++hl++"\n"]
       where hl = generateSelectiveHL srcT (srcLocs (s1:ss))
                  where srcLocs (x:xs) = (srcLoc x):(srcLocs xs)
                        srcLocs []     = []

processConflictSites :: SrcTextData -> [ConflictSites] -> String
processConflictSites srcT (cs:css) =
       case cs of
         Empt       -> processConflictSites srcT css
         CS ch srcs -> (reportIntCheckError srcT (intErrorMsg ch) srcs) ++ 
                       "\n" ++ processConflictSites srcT css
processConflictSites _ [] = ""

data ConflictCounts = CC Char Int

intCounts :: Char -> [ConflictCounts] -> [ConflictCounts]
intCounts ch1 ((CC ch2 count):ccs) =
    case ch1 == ch2 of
      True  -> (CC ch1 (count+1)):ccs
      False -> (CC ch2 count):(intCounts ch1 ccs)
intCounts ch1 [] = [CC ch1 1]

consCSCounts :: [ConflictSites] -> [ConflictCounts] -> [ConflictCounts]
consCSCounts (c:cs) ccs = let ccs' = consCSCounts cs ccs
                          in case c of
                            (CS ch _) -> intCounts ch ccs'
                            _         -> ccs'
consCSCounts [] ccs = ccs

totalCSMsg :: [ConflictSites] -> String
totalCSMsg css = let ccs = consCSCounts css []
                 in "Syntax Error Summary\nTotal number of syntax errors: " ++ 
                    (show (length css)) ++ "\n" ++ printCC ccs
                 where
                    printCC ((CC ch int):ccs) = "   Total no. of " ++  (intErrorMsg ch) ++ 
                                                " : " ++ (show int) ++ "\n" ++ (printCC ccs)
                    printCC [] = ""

idToStr :: [Id] -> [String]
idToStr (id:ids) = (idStr id):(idToStr ids)
idToStr []       = [] 
idToSrc :: [Id] -> [SrcInfo]
idToSrc (id:ids) = (idSrcInfo id):(idToSrc ids)
idToSrc []       = []

srcInfoPair :: Id -> [Id] -> (SrcInfo,SrcInfo)
srcInfoPair id (v:vs) = let idstr1 = idStr id
                            idstr2 = idStr v  
                        in case (idstr1==idstr2) of
                             True  -> ((getSrcInfo id),(getSrcInfo v))
                             False -> srcInfoPair id vs
srcInfoPair _ []      = bug "Problem in ckPat, srcInfoPair"

isABuiltin :: String -> Bool
isABuiltin str = let str' = nub str
                 in case str' of
                     "(,)"           -> True
                     "[]"            -> True
                     "[,]"           -> True
                     ('[':']':'_':_) -> True
                     ('_':_)         -> True
                     ":"             -> True
                     "*"             -> True
                     "|"             -> True
                     _               -> False

--------------------------------------------------------------------------------

-- Internal AST traversal for selective AST constructs. Contains methods
-- to build id environments for the various syntax checks.

class IdDomain idExp where
   constructEnv     :: idExp -> [String]
   constructIdEnv   :: idExp -> [Id]
   constructConsEnv :: idExp -> ([String],[String])
   constructMethEnv :: idExp -> [TCMethods]
   findDataCons     :: idExp -> [String]

   constructEnv e     = let ids = constructIdEnv e
                        in idToStr ids
   constructIdEnv _   = []
   constructConsEnv _ = ([],[])
   constructMethEnv _ = []
   findDataCons _ = []

instance IdDomain a => IdDomain [a] where
   constructIdEnv (x:xs) = (constructIdEnv x)++(constructIdEnv xs)
   constructIdEnv []     = []

   constructConsEnv (x:xs) = let (env1,env2)   = constructConsEnv x
                                 (env1',env2') = constructConsEnv xs
                             in ((env1++env1'),(env2++env2'))
   constructConsEnv []     = ([],[])

   findDataCons (x:xs) = let ids1 = findDataCons x
                             ids2 = findDataCons xs
                         in ids1++ids2
   findDataCons []     = []

   constructMethEnv (x:xs) = let tcm1 = constructMethEnv x
                                 tcm2 = constructMethEnv xs
                             in mergeMethodEnv tcm1 tcm2
   constructMethEnv []     = []

instance IdDomain Dec where
   constructIdEnv (PrimDec _ pv)   = constructIdEnv pv
   constructIdEnv (ValDec _ letB)  = constructIdEnv letB
   constructIdEnv (ClassDec _ cls) = constructIdEnv cls
   constructIdEnv _                = []

   constructConsEnv (DataDec _ dt cons) = let (DataType id _) = dt
                                              (_,env2) = constructConsEnv cons
                                          in ([idStr id],env2)
   constructConsEnv (ClassDec _ cls)    = constructConsEnv cls
   constructConsEnv (ConsDec _ cs)      = constructConsEnv cs
   constructConsEnv _                   = ([],[])

   findDataCons (ValDec _ letB) = findDataCons letB
   findDataCons _               = []

   constructMethEnv (ClassDec _ cls) = constructMethEnv cls
   constructMethEnv _                = []

instance IdDomain Constr where
   constructConsEnv (ConstrCls id _)  = ([idStr id],[])
   constructConsEnv (ConstrData id _) = ([idStr id],[])

instance IdDomain Class where
   constructIdEnv (Class _ _ _ ms) = constructIdEnv ms

   constructConsEnv (Class _ pred _ _) = let (Pred _ id _) = pred
                                         in ([idStr id],[])

   constructMethEnv (Class _ pred _ ms) = 
              let (Pred _ id _) = pred
              in case (idStr id) of
                   "Chameleon.Primitive.Eq"  -> []
                   "Chameleon.Primitive.Num" -> []
                   _                         -> case (constructMethEnv ms) of 
                                                  [(Meth ids)] -> [TCM id ids]
                                                  _            -> [TCM id []]

instance IdDomain Method where
   constructIdEnv (Method id _) = [id]

   constructMethEnv (Method id _) = [Meth [id]]

instance IdDomain PrimVal where
   constructIdEnv (Prim id _ _) = [id]

instance IdDomain DataType where
   constructIdEnv (DataType _ ts) = constructIdEnv ts

instance IdDomain Cons where
   constructConsEnv (Cons _ _ _ dt) = let (DataType id _) = dt
                                      in ([],[idStr id])

instance IdDomain Pred where
   constructIdEnv (Pred _ _ ts) = constructIdEnv ts

instance IdDomain Type where
   constructIdEnv (VarType id) = [id]
   constructIdEnv _            = []

instance IdDomain Id where
   constructIdEnv id = [id]

instance IdDomain LetBnd where
   constructIdEnv (LetBnd _ id _)        = [id]
   constructIdEnv (LetBndAnn _ id _ _ _) = [id]   

   findDataCons (LetBnd _ _ e)        = findDataCons e
   findDataCons (LetBndAnn _ _ _ _ e) = findDataCons e

instance IdDomain Match where
   constructIdEnv (Match ps _) = constructIdEnv ps

   findDataCons (Match ps e)  = let ids1 = findDataCons ps
                                    ids2 = findDataCons e
                                in ids1++ids2

instance IdDomain Pat where
   constructIdEnv (VarPat id)     = [id]
   constructIdEnv (ConPat _ _ ps) = constructIdEnv ps
   constructIdEnv (AnnPat _ id _) = [id]
   constructIdEnv _               = []

   findDataCons (ConPat _ id ps)  = let ids = findDataCons ps
                                    in (idStr id):ids
   findDataCons _                 = []  

instance IdDomain Exp where
   constructIdEnv (VarExp id)      = [id]
   constructIdEnv (AppExp _ e1 e2) = (constructIdEnv e1)++(constructIdEnv e2)
   constructIdEnv _                = []

   findDataCons (ConExp id)         = [idStr id]
   findDataCons (AppExp _ e1 e2)    = (findDataCons e1)++(findDataCons e2)
   findDataCons (AbsExp _ _ e)      = findDataCons e
   findDataCons (LetExp _ letBs e)  = (findDataCons letBs)++(findDataCons e)
   findDataCons (CaseExp _ es ms)   = (findDataCons es)++(findDataCons ms)
   findDataCons _                   = []

-- Internal AST traversal that defines the various method overloads for the selected 
-- internal syntax constructs.
-- Defined methods:
--
--   varNotInScopeCheck env intexp, checks for variables not in scope (inclusive of 
--   type variables), where
--         intexp - Internal AST constructs.
--         env    - List of bounded variables in current environment.
--
--   patternVarCheck env intexp, checks for non linear pattern variables in LHS of
--   value declarations, as well as class declaration heads and data type declarations, 
--   where
--         intexp - Internal AST constructs.
--         env    - List of pattern variables (Id) in current environment.
--
--   dupConsCheck (env1,env2) intexp, checks for duplicate declarations of type classes, type
--   constructors, data constructors and type annotations, where
--         intexp - Internal AST constructs.
--         env1   - List of type level identifiers (Id) in current environment.
--         env2   - List of value level identifiers (Id) in current environment.
--
--   missingConsCheck (env1,env2) intexp, checks for missing occurrences of data constructor
--   and type class declarations, where
--         intexp - Internal AST constructs.
--         env1   - List of available type classes.
--         env2   - List of available data constructors.
--
--   missingMethodCheck tcenv intexp, checks for missing method definitions in type class
--   instances, where
--         intexp - Internal AST constructs.
--         tcenv  - An environment of type class id mapping to respective method ids.
--
--   dupMethodCheck env intexp, checks for duplicate method declarations in type classes, where
--         intexp - Internal AST constructs.
--         env    - Environment of type class methods

class IntSyntaxCheckDomain intExp where
   varNotInScopeCheck :: [String] -> intExp -> [ConflictSites]
   patternVarCheck    :: [Id] -> intExp -> ([Id],[ConflictSites])   
   dupConsCheck       :: ([Id],[Id]) -> intExp -> ([Id],[Id],[ConflictSites])
   missingConsCheck   :: ([String],[String]) -> intExp -> [ConflictSites]
   missingMethodCheck :: [TCMethods] -> intExp -> [ConflictSites]
   dupMethodCheck     :: Bool -> [IntEnv] -> intExp -> ([IntEnv],[ConflictSites])

   varNotInScopeCheck _ _ = []
   patternVarCheck _ _    = ([],[])
   dupConsCheck _ _       = ([],[],[])
   missingConsCheck _ _   = []
   missingMethodCheck _ _ = []
   dupMethodCheck _ _ _   = ([],[])

instance IntSyntaxCheckDomain a => IntSyntaxCheckDomain [a] where
   varNotInScopeCheck env (x:xs) = 
        (varNotInScopeCheck env x)++(varNotInScopeCheck env xs) 
   varNotInScopeCheck env [] = []

   patternVarCheck env (x:xs) = let (env',cs1) = patternVarCheck env x
                                in let (env'',cs2) = patternVarCheck env' xs
                                   in (env'',cs1++cs2)
   patternVarCheck env [] = (env,[])

   dupConsCheck (env1,env2) (x:xs) = 
        let (env1',env2',cs1)  = dupConsCheck (env1,env2) x
            (env1'',env2'',cs2)= dupConsCheck (env1',env2') xs
        in (env1'',env2'',cs1++cs2)
   dupConsCheck (env1,env2) [] = (env1,env2,[])

   missingConsCheck envs (x:xs) = 
        let cs1 = missingConsCheck envs x
            cs2 = missingConsCheck envs xs
        in cs1++cs2
   missingConsCheck envs [] = []

   missingMethodCheck tcenv (x:xs) = 
        let cs1 = missingMethodCheck tcenv x
            cs2 = missingMethodCheck tcenv xs
        in cs1++cs2
   missingMethodCheck _ [] = []

   dupMethodCheck b env (x:xs) = let (env',cs1)  = dupMethodCheck b env x
                                     (env'',cs2) = dupMethodCheck b env' xs
                                 in (env'',(cs1++cs2))
   dupMethodCheck b env []     = (env,[])

instance IntSyntaxCheckDomain Dec where
   varNotInScopeCheck _ (DataDec _ dt cons) = 
            let env = constructEnv dt
            in concatMap (varNotInScopeCheck env) cons
   varNotInScopeCheck _ (ClassDec _ cls)  = varNotInScopeCheck [] cls
   varNotInScopeCheck env (ValDec _ letB) = varNotInScopeCheck env letB
   varNotInScopeCheck _ _                 = []

   patternVarCheck _ (DataDec _ dt cons) = patternVarCheck [] dt
   patternVarCheck _ (ClassDec _ cls)    = patternVarCheck [] cls
   patternVarCheck _ (ValDec _ letB)     = patternVarCheck [] letB
   patternVarCheck _ _                   = ([],[])

   dupConsCheck envs (DataDec _ dt cons) = let (env1,_,cs1) = dupConsCheck envs dt
                                               (_,env2,cs2) = dupConsCheck envs cons
                                           in (env1,env2,cs1++cs2)
   dupConsCheck envs (ClassDec _ cls)    = dupConsCheck envs cls
   dupConsCheck envs (ValDec _ letB)     = dupConsCheck envs letB
   dupConsCheck (env1,env2) _            = (env1,env2,[])

   missingConsCheck envs (DataDec _ _ cons) = missingConsCheck envs cons
   missingConsCheck envs (ClassDec _ cls)   = missingConsCheck envs cls
   missingConsCheck envs (ValDec _ letB)    = missingConsCheck envs letB
   missingConsCheck envs (InstDec _ inst)   = missingConsCheck envs inst
   missingConsCheck envs (RuleDec _ rule)   = missingConsCheck envs rule
   missingConsCheck envs _                  = []

   missingMethodCheck tcenv (InstDec _ inst) = missingMethodCheck tcenv inst
   missingMethodCheck _ _                    = []

   dupMethodCheck b env (ClassDec _ cls) = case b of
                                             True  -> dupMethodCheck b env cls
                                             False -> (env,[])
   dupMethodCheck b env (ValDec _ letB)  = case b of
                                             True  -> (env,[])
                                             False -> dupMethodCheck b env letB
   dupMethodCheck b env _                = (env,[])

instance IntSyntaxCheckDomain Cons where
   varNotInScopeCheck env (Cons _ ids cnts dt) = 
            let env' = env ++ (constructEnv ids)
            in (varNotInScopeCheck env' dt) ++ (varNotInScopeCheck env' cnts)

   dupConsCheck (env1,env2) (Cons _ _ _ dt) =
            let (DataType id _) = dt
            in case (idStr id) `elem` (idToStr env2) of
                 True  -> let (src1,src2) = srcInfoPair id env2
                          in (env1,env2,[CS '4' [src1,src2]])
                 False -> (env1,(id:env2),[])

   missingConsCheck envs (Cons _ _ cnst dt) = let cs1 = missingConsCheck envs cnst
                                                  cs2 = missingConsCheck envs dt
                                              in cs1++cs2

instance IntSyntaxCheckDomain DataType where
   varNotInScopeCheck env (DataType _ ts) =
            concatMap (varNotInScopeCheck env) ts

   patternVarCheck _ (DataType _ ts) = patternVarCheck [] ts

   dupConsCheck (env1,env2) (DataType id _) = 
            case (idStr id) `elem` (idToStr env1) of
              True  -> let (src1,src2) = srcInfoPair id env1
                       in (env1,env2,[CS '5' [src1,src2]])
              False -> ((id:env1),env2,[])

   missingConsCheck envs (DataType _ ts) = missingConsCheck envs ts

instance IntSyntaxCheckDomain Class where
   varNotInScopeCheck _ (Class ctxt pred fds _) =
            let env = constructEnv pred
            in (varNotInScopeCheck env ctxt)++(varNotInScopeCheck env fds)

   patternVarCheck _ (Class _ pred _ _) = patternVarCheck [] pred

   dupConsCheck envs (Class _ pred _ _) = dupConsCheck envs pred 

   missingConsCheck envs (Class ctxt _ _ md) = let cs1 = missingConsCheck envs ctxt
                                                   cs2 = missingConsCheck envs md
                                               in cs1++cs2

   dupMethodCheck b env (Class _ pred _ md) = 
          let (Pred src _ _) = pred
          in dupMethodCheckInt [src] env md
          where
             dupMethodCheckInt srcs1 env (m:ms) =
                  let (Method id _) = m
                      (env',cs) = dupMethodCheckInt srcs1 env ms
                  in case (idStr id) `elem` (intEnvToStr env') of
                       True  -> let srcs2 = getHLSrcs (idStr id) env'
                                    src   = idSrcInfo id
                                in (env',(CS 'C' ((src:srcs1)++srcs2)):cs)
                       False -> let str = idStr id
                                    src = idSrcInfo id
                                in ((IntEnv str (src:srcs1)):env',cs)
             dupMethodCheckInt _ env [] = (env,[])

instance IntSyntaxCheckDomain Type where
   varNotInScopeCheck env (VarType id) = 
            case ((idStr id) `elem` env) of
               True  -> []
               False -> [CS '1' [idSrcInfo id]]
   varNotInScopeCheck env (AppType _ t1 t2) =
            let r1 = varNotInScopeCheck env t1
                r2 = varNotInScopeCheck env t2
            in r1++r2 
   varNotInScopeCheck _ _ = []

   patternVarCheck env (VarType id) = case (idStr id) `elem` (idToStr env) of
                                        False  -> ((id:env),[])
                                        True   -> let (src1,src2) = srcInfoPair id env
                                                  in (env,[CS '2' [src1,src2]])
   patternVarCheck _ _              = ([],[])

   missingConsCheck envs (AppType _ t1 t2) = let cs1 = missingConsCheck envs t1
                                                 cs2 = missingConsCheck envs t2
                                             in cs1++cs2
   missingConsCheck (env1,_) (ConType id)  = 
         case ((idStr id) `elem` env1) || (isABuiltin (idStr id)) of
            True  -> []
            False -> [CS '8' [idSrcInfo id]]
   missingConsCheck _ _                    = []

instance IntSyntaxCheckDomain Id where
   varNotInScopeCheck env id = case ((idStr id) `elem` env) of
                                 True  -> []
                                 False -> [CS '1' [idSrcInfo id]]

instance IntSyntaxCheckDomain FunDep where
   varNotInScopeCheck env (FunDep _ ids1 ids2) = 
            (varNotInScopeCheck env ids1) ++ (varNotInScopeCheck env ids2)

instance IntSyntaxCheckDomain Ctxt where
   varNotInScopeCheck env (Ctxt ps) = varNotInScopeCheck env ps

   missingConsCheck envs (Ctxt ps) = missingConsCheck envs ps

instance IntSyntaxCheckDomain Cnst where
   varNotInScopeCheck env (Cnst ps) = varNotInScopeCheck env ps

   missingConsCheck envs (Cnst ps) = missingConsCheck envs ps

instance IntSyntaxCheckDomain Prim where
   varNotInScopeCheck env (PredPrim pr)    = varNotInScopeCheck env pr
   varNotInScopeCheck env (EqPrim _ t1 t2) = 
            (varNotInScopeCheck env t1) ++ (varNotInScopeCheck env t2)

   missingConsCheck envs (PredPrim pr) = missingConsCheck envs pr
   missingConsCheck envs (EqPrim _ t1 t2) = let cs1 = missingConsCheck envs t1
                                                cs2 = missingConsCheck envs t2
                                            in cs1++cs2

instance IntSyntaxCheckDomain Pred where
   varNotInScopeCheck env (Pred _ _ ts) = varNotInScopeCheck env ts
   
   patternVarCheck _ (Pred _ _ ts) = patternVarCheck [] ts

   dupConsCheck (env1,env2) (Pred _ id _) =
            case (idStr id) `elem` (idToStr env1) of
              True  -> let (src1,src2) = srcInfoPair id env1
                       in (env1,env2,[CS '6' [src1,src2]])
              False -> ((id:env1),env2,[])

   missingConsCheck (env1,env2) (Pred src id ts) = 
            let cs = missingConsCheck (env1,env2) ts
            in case (idStr id) `elem` env1 of
                 False -> (CS '9' [(idSrcInfo id),src]):cs
                 True  -> cs                                  

instance IntSyntaxCheckDomain Method where
   missingConsCheck envs (Method _ tschm) = missingConsCheck envs tschm

   --dupMethodCheck b env (Method id _) = case (idStr id) `elem` (idToStr env) of
   --                                        True  -> let (src1,src2) = srcInfoPair id env
   --                                                 in (env,[CS 'C' [src1,src2]])
   --                                        False -> ((id:env),[])

instance IntSyntaxCheckDomain TSchm where
   missingConsCheck envs (TSchm ctxt t) = let cs1 = missingConsCheck envs ctxt
                                              cs2 = missingConsCheck envs t
                                          in cs1++cs2

instance IntSyntaxCheckDomain LetBnd where
   varNotInScopeCheck env (LetBnd _ id exp)        = 
            varNotInScopeCheck (env++[idStr id]) exp
   varNotInScopeCheck env (LetBndAnn _ id _ _ exp) = 
            varNotInScopeCheck (env++[idStr id]) exp

   patternVarCheck _ (LetBnd _ _ exp)        = patternVarCheck [] exp
   patternVarCheck _ (LetBndAnn _ _ _ _ exp) = patternVarCheck [] exp

   dupConsCheck (env1,env2) (LetBndAnn src id _ _ _) = 
            case (idStr id) `elem` (idToStr env2) of
              True  -> let (src1,src2) = srcInfoPair id env2
                       in (env1,env2,[CS '7' [src,src1,src2]])
              False -> (env1,(id:env2),[])
   dupConsCheck (env1,env2) _               = (env1,env2,[]) 

   missingConsCheck envs (LetBnd _ _ exp) = missingConsCheck envs exp
   missingConsCheck envs (LetBndAnn _ _ _ tschm exp) = let cs1 = missingConsCheck envs tschm
                                                           cs2 = missingConsCheck envs exp
                                                       in cs1++cs2

   dupMethodCheck b env (LetBnd _ id _) = case (idStr id) `elem` (intEnvToStr env) of
                                             True  -> let src  = idSrcInfo id
                                                          srcs = getHLSrcs (idStr id) env
                                                      in (env,[CS 'C' (src:srcs)])
                                             False -> (env,[])    
   dupMethodCheck b env (LetBndAnn src id _ _ exp) = dupMethodCheck b env (LetBnd src id exp)

instance IntSyntaxCheckDomain Exp where
   varNotInScopeCheck env (VarExp id) = 
            case (idStr id) `elem` env of
               True  -> []
               False -> case anon (idStr id) of
                          True  -> []
                          False -> [CS '3' [idSrcInfo id]]
                        where anon x = case x of
                                         ('_':_) -> True
                                         _       -> False
   varNotInScopeCheck env (AppExp _ e1 e2) =
            (varNotInScopeCheck env e1) ++ (varNotInScopeCheck env e2)
   varNotInScopeCheck env (AbsExp _ id e) =
            varNotInScopeCheck ((idStr id):env) e 
   varNotInScopeCheck env (LetExp _ letBs e) =
            let env' = env ++ (constructEnv letBs)
            in  (varNotInScopeCheck env' letBs)++ (varNotInScopeCheck env' e)                
   varNotInScopeCheck env (CaseExp _ es ms) =
            let env' = env ++ (constructEnv es)
            in  (varNotInScopeCheck env es)++  (varNotInScopeCheck env' ms)
   varNotInScopeCheck _ _ = []

   patternVarCheck _ (AppExp _ e1 e2)  = let (_,cs1) = patternVarCheck [] e1
                                             (_,cs2) = patternVarCheck [] e2
                                         in ([],cs1++cs2)
   patternVarCheck _ (AbsExp _ _ e)    = patternVarCheck [] e
   patternVarCheck _ (LetExp _ lbs e)  = let (_,cs1) = patternVarCheck [] lbs
                                             (_,cs2) = patternVarCheck [] e
                                         in ([],cs1++cs2)
   patternVarCheck _ (CaseExp _ es ms) = let (_,cs1) = patternVarCheck [] es
                                             (_,cs2) = patternVarCheck [] ms
                                         in ([],cs1++cs2)
   patternVarCheck _ _                 = ([],[])

   missingConsCheck (_,env2) (ConExp id)    = 
          case ((idStr id) `elem` env2) || (isABuiltin (idStr id)) of
            True  -> []
            False -> [CS '0' [idSrcInfo id]]
   missingConsCheck envs (AppExp _ e1 e2)   = let cs1 = missingConsCheck envs e1
                                                  cs2 = missingConsCheck envs e2
                                              in cs1++cs2
   missingConsCheck envs (AbsExp _ _ e)     = missingConsCheck envs e
   missingConsCheck envs (LetExp _ letBs e) = let cs1 = missingConsCheck envs letBs
                                                  cs2 = missingConsCheck envs e
                                              in cs1++cs2
   missingConsCheck envs (CaseExp _ es ms)  = let cs1 = missingConsCheck envs es
                                                  cs2 = missingConsCheck envs ms
                                              in cs1++cs2
   missingConsCheck _ _                     = []

instance IntSyntaxCheckDomain Match where
   varNotInScopeCheck env (Match ps e)  = let env' = env ++ (constructEnv ps) 
                                          in varNotInScopeCheck env' e 

   patternVarCheck _ (Match ps e) = let (_,cs1) = patternVarCheck [] ps
                                        (_,cs2) = patternVarCheck [] e
                                    in ([],cs1++cs2)

   missingConsCheck envs (Match ps e) = let cs1 = missingConsCheck envs ps
                                            cs2 = missingConsCheck envs e
                                        in cs1++cs2

instance IntSyntaxCheckDomain Pat where
   patternVarCheck env (VarPat id) = case (idStr id) `elem` (idToStr env) of
                                       True  -> let (src1,src2) = srcInfoPair id env
                                                in (env,[CS '2' [src1,src2]])
                                       False -> case anon (idStr id) of
                                                  True  -> (env,[])
                                                  False -> ((id:env),[])
                                                where anon x = case x of
                                                                 ('_':_) -> True
                                                                 _       -> False
   patternVarCheck env (AnnPat _ id _) = case (idStr id) `elem` (idToStr env) of
                                         True  -> let (src1,src2) = srcInfoPair id env
                                                  in (env,[CS '2' [src1,src2]])
                                         False -> case anon (idStr id) of
                                                  True  -> (env,[])
                                                  False -> ((id:env),[])
                                                where anon x = case x of
                                                                 ('_':_) -> True
                                                                 _       -> False
   patternVarCheck env (ConPat _ _ ps) = patternVarCheck env ps
   patternVarCheck env (LitPat _)      = (env,[]) 

   missingConsCheck (env1,env2) (ConPat _ id ps) = 
                let cs = missingConsCheck (env1,env2) ps
                in case ((idStr id) `elem` env2) || isABuiltin (idStr id) of
                     True  -> cs
                     False -> (CS '0' [idSrcInfo id]):cs
   missingConsCheck _ _ = []

instance IntSyntaxCheckDomain Rule where
   missingConsCheck envs (SimpRule ctxt cnst) = let cs1 = missingConsCheck envs ctxt
                                                    cs2 = missingConsCheck envs cnst
                                                in cs1++cs2
   missingConsCheck envs (PropRule ctxt cnst) = let cs1 = missingConsCheck envs ctxt
                                                    cs2 = missingConsCheck envs cnst
                                                in cs1++cs2

instance IntSyntaxCheckDomain Inst where
   missingConsCheck envs (Inst ctxt pred wh) = let cs1 = missingConsCheck envs ctxt
                                                   cs2 = missingConsCheck envs pred 
                                                   cs3 = missingConsCheck envs wh
                                               in cs1++cs2++cs3

   missingMethodCheck tcenv (Inst ctxt pred wh) = 
          let ids1 = getMethodIds wh
              (Pred src id _) = pred
          in case (findMatch id tcenv) of
               [(TCM id' ids2)] -> let missIds = matchMethods ids1 ids2
                                       unknIds = matchMethods ids2 ids1
                                       srcs    = [(idSrcInfo id),(idSrcInfo id')]
                                   in (makeMethError 'A' missIds srcs) ++ (makeMethError 'B' unknIds srcs)
               _                -> []
          where
             getMethodIds (dec:decs) = 
                 case dec of
                   (ValDec _ letB) -> let (LetBnd _ id _) = letB
                                      in id:(getMethodIds decs)
                   _               -> getMethodIds decs
             getMethodIds [] = []
             findMatch id ((TCM id' ids):tcms) =
                 case (idStr id) == (idStr id') of
                   True  -> [(TCM id' ids)]
                   False -> findMatch id tcms 
             findMatch id [] = []
             matchMethods (id1:ids1) ids2 =
                 let match1 = matchMethodsInt id1 ids2
                 in (matchMethods ids1 match1)
                 where 
                   matchMethodsInt id1 (id2:ids) =
                      case (idStr id1) == (idStr id2) of
                        True  -> matchMethodsInt id1 ids
                        False -> id2:(matchMethodsInt id1 ids)
                   matchMethodsInt id1 [] = []
             matchMethods [] ids = ids
             makeMethError ch (id:ids) srcs = [CS ch ((idToSrc (id:ids))++srcs)]
             makeMethError _ [] _           = []
