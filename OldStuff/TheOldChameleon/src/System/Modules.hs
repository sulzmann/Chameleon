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
-- ModuleName related stuff. Calculating dependencies etc.
--
-- FIXME: We ought to try reading modules from directories other than the
--	  current one. e.g. there should be a standard location we try reading
--	  standard modules like the Prelude from. We should also have a 
--	  commandline flag which extends the directories searched through.
--
--------------------------------------------------------------------------------

module System.Modules (
    moduleBatches, Batch, ModuleName,
    tryToReadModule
)
where

import List  (nub)
import Maybe
import qualified Data.Set as Set
import qualified Data.HashTable as HT

import AST.ChParser.Parser
import qualified AST.External as AST
import AST.SrcInfo

import Misc
import Misc.Files
import Misc.Error
import Misc.Result
import Misc.ErrorMsg
import Misc.Defaults

--------------------------------------------------------------------------------

-- module name
type ModuleName = String

-- a module dependency graph: maps a module to all modules it imports
type DGraph = HT.HashTable ModuleName [ModuleName]

instance Show (HT.HashTable a b) where
    show _ = "HT"

dgraphToList :: DGraph -> IO [(ModuleName, [ModuleName])]
dgraphToList = HT.toList

duplicateDGraph :: DGraph -> IO DGraph
duplicateDGraph dg = do
    l <- HT.toList dg
    HT.fromList HT.hashString l

printDGraph :: DGraph -> IO ()
printDGraph dg = do
    xs <- dgraphToList dg
    print xs

----------------------------------------

-- update an entry
updateDGraph :: DGraph -> (ModuleName, [ModuleName]) -> IO ()
updateDGraph dg (id,ids) = do
    mv <- HT.lookup dg id
    cs <- case mv of
		Nothing -> return []
		Just xs -> do HT.delete dg id
			      return xs
    let ids' = let ids' = [ id | id <- nub ids, id `notElem` cs ]
	       in  cs ++ ids'
    HT.insert dg id ids'


--------------------------------------------------------------------------------

-- builds a single-step (unnormalised) module dependency graph
-- NOTE: we pass in the Id of the module as it appeared in an import dec. (so
-- that, in case of an error, we can report the relevant source location.)

buildDGraph :: [FilePath] -> AST.Id -> IO (SimpleResult DGraph)
buildDGraph paths mid = do
    dg <- HT.new (==) HT.hashString
    build dg mid
  where
    build :: DGraph -> AST.Id -> IO (SimpleResult DGraph)
    build dg mid = do
	let m = AST.idStr mid 
	-- check if we've already done this module
	mims <- HT.lookup dg m
	case mims of
	    Just _  -> return2 dg	-- we've already processed m
	    Nothing -> do
		-- read the module
		esrc <- tryToReadModule paths mid
			-- readFileContentsSrc (m ++ defaultFilenameExtension) 
			-- 		    (AST.idSrcInfo mid)
		case esrc of
		  Failure e1 b -> return (Failure e1 b)
		  Success e1 src -> do
		    -- parse imports
		    case parseImportsOnly m 1 src of
		      Failure e2 b -> return (Failure (e1++e2) b)
		      Success e2 (_,_,ims) -> do
			let ids = [ id | AST.Import id _ _ <- ims ]
			-- update graph
			HT.insert dg m (map AST.idStr ids)
			-- build all sub-graphs, if any failed, then we fail
			ress <- mapM (build dg) ids
			let fs = filter isFailure ress
			if null fs
			  then return (Success (e1++e2) dg)
			  else let es = concatMap resultErrors fs
			       in  return (simpleFailure es)

--------------------------------------------------------------------------------

-- builds the transitive closure of the graph, returns a new graph
normaliseDGraph :: DGraph -> IO DGraph
normaliseDGraph dg0 = do	
    dg <- duplicateDGraph dg0
    mis <- HT.toList dg
    let (ms,_) = unzip mis
    mapM_ (proc dg) ms
    return dg
  where
    proc :: DGraph -> ModuleName -> IO ()
    proc dg c = do cs <- trans [] c
		   updateDGraph dg (c,cs)
      where
        trans ms m = do
	    ms1 <- importees m
	    let ms2 = nub ms1
	    if all (`elem`ms) ms2
	      then -- fixpoint reached
		   return ms
	      else do ms3 <- thread (ms2++ms) ms2
		      return (nub ms3)
	  where
	    thread ms []     = return ms
	    thread ms (d:ds) = do
		ms1 <- trans ms d
		let ms2 = nub (ms1 ++ ms)
		thread ms2 ds
  
	-- modules imported by m
	importees m = do 
	    mms <- HT.lookup dg m
	    return $ case mms of
			Nothing -> []
			Just ms -> ms

--------------------------------------------------------------------------------

-- A Batch is a list of modules which must be processed simultaneously 
-- (i.e. because they are cyclically dependant)
type Batch = [ModuleName]

-- hostory of modules already processed
type Hist  = Set.Set ModuleName

-- Given an initial module, generates a list of batches which ensures that
-- each module's dependencies are met before it is processed.
-- The boolean argument, if True, causes `implicit' modules to be imported.
-- (This is the default system behaviour.)
moduleBatches :: Bool -> [FilePath] -> ModuleName -> IO (SimpleResult [Batch])
moduleBatches imp paths m = do
    res_dg <- buildDGraph paths (AST.anonId m)
    case res_dg of
      Failure e	a  -> return (Failure e a)
      Success e dg -> do bs <- batches dg
			 let bs' | imp = implicitImports : bs
				 | otherwise = bs
			 return (Success e bs')
  where	
    batches dg = do
	ndg <- normaliseDGraph dg
	-- process module/node m, hs are modules already visited
	let proc :: Hist -> [Batch] -> ModuleName -> IO (Hist, [Batch])
--	    proc hs bs m | m `Set.elementOf` hs = return (hs,bs)
	    proc hs bs m | m `Set.member` hs = return (hs,bs)
			 | otherwise = do
		mis <- HT.lookup dg m
		let is  = fromJust mis
--		    hs1 = Set.addToSet hs m
		    hs1 = (flip Set.insert) hs m
		-- check if m is in a cycle
		mcs <- cycle m
		case mcs of
		    Nothing -> do
			-- process imports, add singleton batch
			(hs2,bs1) <- thread hs1 bs is
			return (hs2, [m]:bs1)
		    
		    Just cs -> do
			-- it's a cycle, first process non-cyclical dependencies
			let is1 = filter (`notElem`cs) is
			(hs2,bs1) <- thread hs1 bs is1
			-- process each cycle member individually, not allowing
			-- any to reach back into the cycle
			miss <- mapM (HT.lookup dg) cs
			let is2 = concat (map fromJust miss)
--			    hs3 = Set.mkSet cs `Set.union` hs2
			    hs3 = Set.fromList cs `Set.union` hs2
			(hs4,bs2) <- thread hs3 bs1 is2 
			return (hs4,cs:bs2)
	      where
		threadH :: Hist -> [Batch] -> [(ModuleName,Hist)] 
			-> IO (Hist, [Batch])
		threadH hs bs [] = return (hs,bs)
		threadH hs bs ((m,h):mhs) = do
		    (hs1, bs1) <- proc (h `Set.union` hs) bs m
--		    let hs2 = hs1 `Set.minusSet` h
		    let hs2 = hs1 `Set.difference` h
		    threadH hs2 bs1 mhs

		thread :: Hist -> [Batch] -> [ModuleName] -> IO (Hist, [Batch])
		thread hs bs [] = return (hs,bs)
		thread hs bs (m:ms) = do
		    (hs',bs') <- proc hs bs m
		    thread hs' bs' ms

		-- returns nothing if m is not in a cycle, 
		-- else all the modules in the cycle
		cycle :: ModuleName -> IO (Maybe [ModuleName])
		cycle m = do
		    mis <- HT.lookup ndg m
		    let is = fromJust mis
		    if isNothing mis || m `notElem` is then return Nothing
		      else do
			miss <- mapM (HT.lookup ndg) is
			let iss = map fromJust miss
			    cs = [ c | (c,is) <- zip is iss, m `elem` is ]
			return (Just cs)
    
--	(_, bs) <- proc Set.emptySet [] m
	(_, bs) <- proc Set.empty [] m
	return (reverse bs)

--------------------------------------------------------------------------------

-- Given a list of paths to search in, attempts to load the nominated module.
tryToReadModule :: [FilePath] -> AST.Id -> IO (SimpleResult String)
tryToReadModule ps m = try ps
  where
    id   = AST.idStr m
    fn   = addChSuffix (moduleToPath id)
    info = getSrcInfo m
    
    try [] = let msg = errorMsgLine info ["Could not load module `"++id++"'"]
		 err = Error SuperFatal info msg
	     in  return (simpleFailure [err])
	     
    try (p:ps) = do
	let path = inPath [p] fn
--	putStrLn ("try to load: " ++ path)
	res <- readFileContentsSrc path info
	case res of
	    Err e    -> try ps
	    Succ str -> return (mkSuccess str)
