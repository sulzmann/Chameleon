--------------------------------------------------------------------------------
--
-- Copyright (C) 2005 The Chameleon Team
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
-- Implements the standard Chameleon pipeline.
-- The pipeline processes a single module batch from parsing to backend output.
--
--------------------------------------------------------------------------------

module System.Pipeline
where

import List
import IO
import Monad
import Maybe
import System

import System.Control

import Misc
import Misc.Files
import Misc.Result
import Misc.Error
import Misc.ErrorMsg
import Misc.Print
import Misc.Output.ANSI

import Core.BuiltIn
import Config.Global as Conf

import AST.SrcInfo
import AST.Common   (idStr, anonId, Id)
import AST.Internal (addToAllModules, Prog, Dec, ModType(..))
import AST.External (hasXModule,collectSrcInfos)
import AST.LocInfo  (progLocInfo, LocInfo)

-- modules
import AST.Exports
import System.Modules

-- parsing the source file
import AST.ChParser.Parser

-- external AST checks
import AST.ExtChecks

-- XHaskell translation
import X.XTrans
import X.XResult

-- desugaring
import AST.Desugarer

-- module export processing
import AST.Exports

-- internal AST checks
import AST.IntChecks

-- internal AST analysis
import AST.CallGraph

-- CHR generation
import Core.CHRGenerator
import Core.Constraint

-- type inference
import Core.Solver
import Core.InfGoal
import Core.Inference
import Core.InfResult
import TypeError.ErrorMsg

-- kind validation Stuff
import qualified Core.Kinds as Kinds

-- evidence translation
import Core.Evidence

-- back-ends
import AST.Reorder
import Backends.Cleanup
import qualified Backends.Scheme.GenerateStrict as Scheme
import qualified Backends.Scheme.GenerateLazy   as SchemeLazy
import Backends.Lvm.ToLvmCore 
-- import qualified Backends.Scheme.Generate as Scheme

--------------------------------------------------------------------------------

-- process all module batches
processBatches :: Sys ()
processBatches = do
    stSet modules' []
    bs <- stGet batches
    proc bs
  where
    proc [] = stSet batches' []
    proc bbs@(b:bs) = do
        stSet batches' bbs
        case b of
            [m] -> processModule m
            ms  -> processCycle b
        proc bs

----------------------------------------

-- process a singleton batch
processModule :: ModuleName -> Sys ()
processModule m = do
    let fn = addChSuffix m
    verb1 ("Processing module in `" ++ fn ++ "'")
    stSet srcFilename' fn
    getSourceText m
    parseSourceText
    checkExternalAST
    desugarExternalAST
    analyseInternalAST
    validateKinds
    b <- isXHaskellMod
    if b -- FIXME: we check after analyseIntAST
       then do
            verb1 "This is a xhaskell module"
            collectSrcInfo
--            ast <- stGet intProg
--            doIO (putStrLn (pretty ast))
            xhaskellTranslate
--            ast <- stGet intProg
--            doIO (putStrLn (pretty ast))
       else do  
            verb1 "This is not a xhaskell module"
            validateTypes
    evidenceTranslation
    backEnd

----------------------------------------
-- process a cycle of modules
processCycle :: Batch -> Sys ()
processCycle = bug "Support for cyclical modules not implemented yet!"

--------------------------------------------------------------------------------
-- pipeline stages
--------------------------------------------------------------------------------

-- read the source file
getSourceText :: ModuleName -> Sys ()
getSourceText m = do 
    ps   <- getConfig modulePaths
    esrc <- doIO (tryToReadModule ps (anonId m))
    case esrc of
	Failure es b -> causeFailure es
	Success es src -> do
	    doIO (reportErrors es)
	    stSet srcProg' src

--------------------------------------------------------------------------------

-- parse source, generating external AST
parseSourceText :: Sys ()
parseSourceText = do
    verb1 "Parsing source code"
    src <- stGet srcProg
    fn <- stGet srcFilename 
    n  <- freshInt
    let eres = parseProg fn n src
    case eres of
	Failure es b -> causeFailure es
	Success es (_rest, scs, n, ast, toks) -> do 
	    stSet uniqueInt' n
	    doIO (reportErrors es)
	    stSet extProg' ast
	    stSet srcCommands' scs
	    stSet srcTokens' toks
	    verb 4 [show ast]

--------------------------------------------------------------------------------

-- check external AST
checkExternalAST :: Sys ()
checkExternalAST = do 
    verb1 "Checking external AST"
    return ()


-------------------------------------------------------------------------------

-- check whether is an xmodule
isXHaskellMod :: Sys Bool
isXHaskellMod = do 
  ext_ast <- stGet extProg
  return (hasXModule ext_ast)


-------------------------------------------------------------------------------

-- collect SrcInfo table explicitly for Xhaskell module

collectSrcInfo :: Sys ()
collectSrcInfo = do
  ext_ast <- stGet extProg
  stSet srcInfos' (mkSrcInfoTable (collectSrcInfos ext_ast))
  return ()

--------------------------------------------------------------------------------

-- XHaskell translation
xhaskellTranslate :: Sys ()
xhaskellTranslate = do 
   verb1 "XHaskell Translation"
   int_ast <- stGet intProg
   n <- stGet uniqueInt
   (res, impdecs) <- getImportedTypeInfo
   cres <- filterM (\ (id,_) -> isHaskellId id) res
   xres <- filterM (\ (id,_) -> isXHaskellId id) res
   let xresult = xtrans n cres xres impdecs int_ast
   case xresult of 
       XFailure es -> do
             verb1 "xhaskell translation failed."
             sd <- getSrcTextData
             let errs = map (xerror2error sd) es
             causeFailure errs
       XSuccess es (st, int_ast) -> do
             verb1 "xhaskell translation succeed."
             let n' = num st
             stSet uniqueInt' n' 
             stSet intProg' int_ast 
             let (REState _ _ _ _ infres _) = st
             d <- currentModuleName 
             Just (ModuleInfo n t fn exs ims mi _) <- getModuleInfoById d
             replaceModuleInfo (ModuleInfo n t fn exs ims mi infres)

--------------------------------------------------------------------------------

-- Extract the module name out of a qualified idStr
getModNameFromIdStr :: String -> String
getModNameFromIdStr idStr = getModNameFromIdStr' [] [] idStr
    where getModNameFromIdStr' :: String -> String -> String -> String
          getModNameFromIdStr' r b [] = r
          getModNameFromIdStr' r b ('.':cs) = getModNameFromIdStr' (r++b) ['.'] cs
          getModNameFromIdStr' r b (c:cs) = getModNameFromIdStr' r (b++[c]) cs

--------------------------------------------------------------------------------

-- isHaskellId/isXHaskellMod: test whether an Id is imported from a Haskell/XHaskell module.
-- Precondition: the given module has already processed.
isHaskellId :: String -> Sys Bool
isHaskellId i = do
             let mid = getModNameFromIdStr i
             Just (ModuleInfo _ mt _ _ _ _ _) <- getModuleInfoById mid
             case mt of
               Cmod -> return True
               _    -> return False

isXHaskellId :: String -> Sys Bool
isXHaskellId i = do 
             let mid = getModNameFromIdStr i
             Just (ModuleInfo _ mt _ _ _ _ _) <- getModuleInfoById mid
             case mt of
               Xmod -> do 
                       return True
               _    -> return False
             

--------------------------------------------------------------------------------

-- desugar the external AST, converting it to an internal AST
desugarExternalAST :: Sys ()
desugarExternalAST = do
    verb1 "Desugaring AST"
    ext_ast <- stGet extProg
    opts    <- stGet config
    let (int_ast, info) = desugarProg opts ext_ast
    -- verb 3 [show int_ast]
    verb 3 ["\n" ++ pretty int_ast]
    stSet intProg' int_ast
    stSet srcInfos' info

--------------------------------------------------------------------------------

-- analyse internal AST: 
--  - perform various syntactic checks
--  - find all names/declarations in scope
--  - fully qualify all module names
--  - find all actual exports (top-level things)
--  - identify all let-bound vars.
--  - generate call graphs
--  - discover recursive functions
analyseInternalAST :: Sys ()
analyseInternalAST = do
    verb1 "Analysing internal AST"
    int_ast <- stGet intProg

    verb1 "Checking internal AST"
    srcT <- getSrcTextData
    -- Delayed to the end of analyseInternalAST
    -- doIO (internalASTChecks int_ast srcT)

    -- this module's name, and filename
    id <- currentModuleName
    fn <- stGet srcFilename

    -- calculate and qualify local (to the module), top-level declarations 
    -- (these aren't necessarily exported)
    let exs  = progExportable int_ast
	qexs = map (qualifyExported id) exs
    verb 3 ["Exports: ", pretty exs]

    mis <- stGet modules
    -- qualify all names
    verb1 "Adding imports and fully qualifying all names"
    let mxs = (id,qexs) : [ (id, exs) | ModuleInfo id _ _ exs _ _ _ <- mis ]
	(int_ast',ims,imxs) = qualifyNamesProg mxs int_ast
    stSet intProg' int_ast' 
    -- re-calculate exports (it's cheap) now that they're name qualified
    let exs = progExports int_ast' -- qexs
    verb 3 ["Names Fully Qualified: ", "\n" ++ pretty int_ast']
    -- decide the type of the module
    b <- isXHaskellMod
    let mt = if b then Xmod else Cmod
    -- add module info
    let mi = ModuleInfo id mt fn exs imxs ims []
    replaceModuleInfo mi
    
    -- call graph stuff
    cg   <- doIO (progCallGraph int_ast')
    ncg  <- doIO (normaliseCallGraph cg)
    ids  <- doIO (callGraphVars cg)
    sccs <- doIO (callGraphSCCs cg)
    rids <- doIO (recursiveVars ncg)
    stSet callGraph' cg
    stSet normCallGraph' ncg
    stSet letIds' ids
    stSet recursiveIds' rids
    stSet sccs' sccs
    verb 1 ("SCCs: " : map pretty sccs)

    let li = progLocInfo int_ast
    stSet locInfo' li

    verb1 "Checking internal AST"
    intChk <- getConfig checkIntSyntax
    when intChk $ do
	impted <- getCurrentImported
        let (imptTypes,imptVals,imptDecs) = buildImportedEnv impted
	    imptTypes' = filterPrimitives imptTypes
            imptVals'  = filterPrimitives imptVals
        --doIO (putStr ("Types: " ++ (pretty imptTypes) ++ "\n"))
        --doIO (putStr ("Values: " ++ (pretty imptVals) ++ "\n"))
        --doIO (putStr ("Declarations: " ++ (pretty imptDecs) ++ "\n"))
        doIO (internalASTChecks imptTypes imptVals imptDecs int_ast' srcT)

--------------------------------------------------------------------------------

validateKinds :: Sys ()
validateKinds = do
    impted <- getCurrentImported
    chk <- getConfig checkKinds
    when chk (do
        --id       <- currentModuleName
        --Just mod <- getModuleInfoById id
        --depMods  <- getAllDepMods (modulesImported mod) id
        let impdecs = filterImports impted
        --doIO (putStr ("\n"++(pretty mod)++"\n"))
	verb1 "Validating kinds"
	int_ast <- stGet intProg
	options <- stGet config
	srcT <- getSrcTextData
	dec <- doIO (Kinds.pile int_ast)
        --doIO (putStr ("Declarations: " ++ (pretty (dec++impdecs)) ++ "\n"))
        let fulldec = dec ++ impdecs
	(verbMsg,es) <- doIO (Kinds.kindValidate srcT fulldec (mimicGHC options))
	-- verb1 verbMsg
	unless (null es) $ do
	   causeFailure es  
     )

getCurrentImported :: Sys [Imported] 
getCurrentImported = do
     id       <- currentModuleName
     Just mod <- getModuleInfoById id
     depMods  <- getAllDepMods (modulesImported mod) id    
     getImportedDecs depMods

getAllDepMods :: [IdStr] -> IdStr -> Sys [IdStr]
getAllDepMods (id:ids) ident = do ids' <- getAllDepMods ids ident
                                  case id==ident of
                                    False -> do mb <- getModuleInfoById id 
                                                case mb of
                                                  Just mod -> return (nub ((modulesImported mod) ++ ids'))
                                                  _        -> do doIO (exit ("Error in " ++ ident ++ ": Cannot import " ++ id ++ "\n"))
                                                                 return []
                                    True  -> do return ids'
getAllDepMods [] _           = return []

getImportedDecs :: [IdStr] -> Sys [Imported]
getImportedDecs (id:ids) = do 
    Just (ModuleInfo _ _ _ xDecs iDecs imps _) <- getModuleInfoById id
    --let xDecs' = filterImports xDecs
    xDecs'   <- getImportedDecs ids
    return (xDecs ++ xDecs')
getImportedDecs []       = return []                            

buildImportedEnv :: [Imported] -> ([Id],[Id],[Dec])
buildImportedEnv (imp:imps) =  
           let (typeIds,valIds,classDecs) = buildImportedEnv imps
           in case imp of
                XVal   id     -> (typeIds,id:valIds,classDecs) 
                XType  id _   -> (id:typeIds,valIds,classDecs)
                XClass id dec -> case isPrimitive (idStr id) of
                                   False -> (typeIds,valIds,dec:classDecs)
                                   True  -> (typeIds,valIds,classDecs)
                                 where 
                                   isPrimitive str = 
                                      case str of
                                        'C':'h':'a':'m':'e':'l':'e':'o':'n':'.':_ -> True
                                        _                                         -> False 
                _             -> (typeIds,valIds,classDecs)
buildImportedEnv []         = ([],[],[])

filterPrimitives :: [Id] -> [Id]
filterPrimitives (id:ids) = 
       case (idStr id) of
         'C':'h':'a':'m':'e':'l':'e':'o':'n':'.':_ -> filterPrimitives ids
         _                                         -> id:(filterPrimitives ids)
filterPrimitives [] = []

filterImports :: [Imported] -> [Dec]
filterImports (imp:imps) = case imp of
                              XType  _ d -> d:(filterImports imps)
                              XClass _ d -> d:(filterImports imps)
                              _          -> filterImports imps
filterImports []         = []

--------------------------------------------------------------------------------
-- Type inference

validateTypes :: Sys ()
validateTypes = do
    is <- getConfig infScheme
    case is of
	W_Based   -> inferAllTypes
	CHR_Based -> do
	    generateCHRsGoals
	    inferAllTypesFromCHRs

----------------------------------------

inferAllTypes :: Sys ()
inferAllTypes = do
    verb1 "Inferring all types"
    sccs    <- stGet sccs
    int_ast <- stGet intProg
    linfo   <- stGet locInfo
    (res, impdecs) <- getImportedTypeInfo
    ers <- doIO (typeInference int_ast linfo res impdecs sccs)
    case ers of
	Failure es _ -> causeFailure es

	-- inference results, and matches
	Success es (res,ms) -> do
	    -- save the result
	    stSet uconsMatches' ms
	    -- putsLn ("ms: " ++ show ms)
	    stSet infResults' res
	    id <- currentModuleName
	    Just (ModuleInfo d t f x i m _) <- getModuleInfoById id
	    replaceModuleInfo (ModuleInfo d t f x i m res)
	    -- deal with the type errors
	    handleTypeErrors
	    -- stop if necessary
	    lastStageInf MaybeStop

----------------------------------------

-- generates all the CHRs and inference goals
-- also simplify the CHRs
generateCHRsGoals :: Sys ()
generateCHRsGoals = do
    verb1 "Generating CHR rules and goals"
    int_ast <- stGet intProg
    recs <- stGet recursiveIds
    (res, impdecs) <- getImportedTypeInfo
    verb 3 ("Imported Non-Val. Decs. " : map pretty impdecs)
    ecgs <- doIO (progCHRsGoals int_ast res impdecs recs)
    case ecgs of
	Failure es _ -> causeFailure es

	Success es (chrs,igs) -> do 
		doIO (reportErrors es)
		let chrs' = builtInCHRs ++ chrs 
		stSet originalCHRs' chrs'
		stSet infGoals' igs
		-- if at verb. level 2 or higher, show the CHRs
		verb 2 (map pretty chrs)
		verb 2 (map pretty igs)

-- gets all imported inference results, and (non-val.) declarations
-- FIXME: doesn't extract types inferred in W style!
--
-- getImportedTypeInfo :: Sys ([(IdStr, (Type,Constraint))], [AST.Dec])
getImportedTypeInfo = do
    id <- currentModuleName
--    doIO $ putStrLn (show id)
    Just (ModuleInfo _ _ _ _ imxs ims _) <- getModuleInfoById id
    jmis <- mapM getModuleInfoById ims
    let imstrs = map (idStr . impId) imxs
	mis = map (fj "X") jmis
	res = [ (f,(t,c)) | ModuleInfo mod_id _ _ _ _ _ irs <- mis, ir <- irs,
			    isInfSuccess ir,
			    let f = idStr (resId ir)
    -- Temp-Fix introduced by luzm and lamsoonl
    -- fixes the error caused by InfSuccessW is applied with resTLV and resCons
				t = (case ir of 
                                     InfSuccessW _ _ _ -> resType ir
                                     InfSuccess _ _ _  -> head (resTLV ir)
                                     _                 -> bug "unknown success")
				c = (case ir of 
                                     InfSuccessW _ _ _ -> trueConstraint
                                     SubSuccess _      -> trueConstraint
                                     _                 -> resCons ir),
			    f `elem` imstrs ]
    -- retrieve all the imported class and type declarations and add them
    let	impdecs = concatMap (maybeToList . impDec) imxs
    return (res, impdecs)

inferAllTypesFromCHRs :: Sys ()
inferAllTypesFromCHRs = do
    verb1 "Inferring all types from CHRs"
    igs  <- stGet infGoals
    -- just do top-level variables
    let igs' = [ ig | ig <- igs, infTop ig ]

    -- we don't generate any simplified CHRs yet
    chrs <- stGet originalCHRs		
    res  <- doIO (runInfGoals chrs igs')
    stSet infResults' res

    -- save the result
    id <- currentModuleName
    Just (ModuleInfo d t f x i m _) <- getModuleInfoById id
    replaceModuleInfo (ModuleInfo d t f x i m res)
    -- deal with the type errors
    handleTypeErrors
    -- stop if necessary
    lastStageInf AlwaysStop
	       
----------------------------------------

-- Handle type errors: generate error messages and throw an error if necessary
handleTypeErrors :: Sys ()
handleTypeErrors = do
    res <- stGet infResults
    let res' = filter Core.InfResult.isFailure res
    unless (null res') $ do
	sd <- getSrcTextData
	es <- doIO (mapM (generateTypeErrorMsg sd) res')
	causeFailure es


-- Find out what the user-specified last stage is supposed to be. If it's
-- ValidateTypes, and we're on the last module batch, we should print the 
-- type information, then stop.
lastStageInf :: Stop -> Sys ()
lastStageInf halt = case halt of
  AlwaysStop -> reportTypes stderr >> stop
  _    -> do
    bs <- stGet batches
    ls <- getConfig lastStage
    let done = singleton bs && ls == ValidateTypes
 
    -- if at verb level 2 or higher, or we're about to stop, report the types
    vb <- asVerboseAs 2
    when (vb || done) (reportTypes stderr)
    when done stop

  where
    stop :: Sys ()
    stop = let err = Error NonFatal anonSrcInfo "Reached final stage"
	   in  causeFailure [err]
  
    reportTypes :: Handle -> Sys ()
    reportTypes h = do 
	res <- stGet infResults
	let out = unlines (map formatInfResult res)
	hPuts h out

--------------------------------------------------------------------------------

evidenceTranslation :: Sys ()
evidenceTranslation = do
    verb1 "Evidence translation"
    li <- stGet locInfo
    ms <- stGet uconsMatches
    int_ast <- stGet intProg
    let int_ast' = translateProg li ms int_ast
    stSet intProg' int_ast'

--------------------------------------------------------------------------------

-- produces target code for current module
backEnd :: Sys ()
backEnd = do
    back  <- getConfig backend
    prog0 <- stGet intProg
    let prog = cleanupAST prog0
    case back of
	NoBackEnd -> return ()

	SchemeBackEnd -> do 
		verb1 "Generating Strict Scheme Code"
		scheme Scheme.generate prog

	SchemeLazyBackEnd -> do
		verb1 "Generating Lazy Scheme Code"
		scheme SchemeLazy.generate prog

	LvmBackEnd -> do
		verb1 "Generating LVM Code"
	        fn <- stGet srcFilename
		doIO $ toLvmCore fn prog
      where
	scheme :: (Prog -> String) -> Prog -> Sys ()
	scheme trans prog = do	      
	    -- first place binding groups in dependency order
	    ncg   <- stGet normCallGraph
	    prog' <- doIO (reorderBindingGroups ncg prog)
	    fn <- stGet srcFilename
	    let fn' = chToSchemeSuffix fn
		out = trans prog'
	    res <- doIO (writeFileContents fn' out)
	    checkE res

--------------------------------------------------------------------------------


{-
test :: Sys ()
test = do
    let a = TVar (mkVar "a")
	b = TVar (mkVar "b")
	k = TVar . mkVar . ('K':) . show 
	star  = TCon (mkFreeName "*")
	arrow = TCon (mkFreeName "->")
	arr t1 t2 = TApp (TApp arrow t1) t2
	
	eqs = [  k 8 =:= (k 6 `arr` (k 7 `arr` star))
		,k 6 =:= k 10
		,k 7 =:= k 11
		,k 10 =:= (k 11 `arr` k 9)
		,k 9  =:= star
		,k 8  =:= (k 1 `arr` (k 2 `arr` star))
		,k 14 =:= (k 12 `arr` (k 13 `arr` star))
		,k 17 =:= (k 1 `arr` (k 2 `arr` star))
		,k 12 =:= k 18
		,k 17 =:= (k 18 `arr` k 16)
		,k 13 =:= k 19
		,k 16 =:= (k 19 `arr` k 15)
		,k 12 =:= k 20
		,k 15 =:= star
		,k 20 =:= star
		,(k 14 =+= (k 4 `arr` (k 5 `arr` star))) (J [14]) ]

	goal = InfGoal (anonId "test") True [] (toConstraint eqs)
    puts ("\ngoal:\n" ++ pretty goal)
    res <- doIO (runInfGoals [] [goal])
    puts ("\n\nres :\n" ++ pretty res ++ "\n\n")
-}
