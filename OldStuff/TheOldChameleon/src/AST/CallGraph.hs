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
-- | Contains the data structure for representing a call graph, as well as
-- constructing a graph from an internal AST.
-- Also exports functions for performing various queries on a call graph.
--
-- NOTE: Since we use Data.Graph to find SCCs, we might as well use it to
-- represent call graphs in the first place!
--------------------------------------------------------------------------------

module AST.CallGraph (
    CallGraph, NormCallGraph,
    progCallGraph, normaliseCallGraph, denormCallGraph,
    callGraphToList, callGraphFromList, duplicateCallGraph,

    callGraphVars, recursiveVars, callGraphSCCs, SCC
)
where

import List
import qualified Data.Graph	as Gr
import qualified Data.HashTable as HT

import AST.Internal
import AST.SrcInfo

--------------------------------------------------------------------------------

-- | maps caller to callees
newtype CallGraph = CG (HT.HashTable Id [Id])

-- | A normalised call graph (represents transitive closure of a standard call
-- graph.) Distinguishing this from a regular call graph ensures we never
-- accidentally pass a standard graph to a function which only works for 
-- a normalised graph.
newtype NormCallGraph = NCG (HT.HashTable Id [Id])

-- a list of all lambda-bound variables in scope
-- (in reverse order, i.e. a stack)
type LVs = [Id]

-- | a list of mutually-dependent variables
type SCC = [Id]

-- identifies the name of the current definition (the current caller),
-- a list of all unbound lambda variables at that point, and the callgraph
type Conf = (Id, LVs, CallGraph)

-- adds calls from id to ids to the call graph
updateCallGraph :: CallGraph -> (Id, [Id]) -> IO ()
updateCallGraph (CG cg) (id,ids) = do
    mv <- HT.lookup cg id
    cs <- case mv of
		Nothing -> return []
		Just xs -> do HT.delete cg id
			      return xs
    let ids' = let ids' = [ id | id <- nubIds ids, not (any (id`eq`) cs) ]
	       in  cs ++ ids'
    HT.insert cg id ids'
    
-- threads the current configuration through multiple calls
multiple :: (Conf -> a -> IO LVs) -> Conf -> [a] -> IO LVs
multiple f (c,lvs,cg) [] = return lvs
multiple f conf@(c,lvs,cg) (x:xs) = do 
    lvs' <- f conf x 
    multiple f (c,lvs',cg) xs
    
-- hash :: Id -> Int32
hash = HT.hashString . idStr

eq :: Id -> Id -> Bool
eq id1 id2 = idStr id1 == idStr id2

nubIds :: [Id] -> [Id]
nubIds = nubBy eq

--------------------------------------------------------------------------------

-- | generates a callgraph for the given program
progCallGraph :: Prog -> IO CallGraph
progCallGraph = cgProg

-- | turns a callgraph into an association list
callGraphToList :: CallGraph -> IO [(Id, [Id])]
callGraphToList (CG cg) = HT.toList cg

-- | generates a callgraph from an association list 
-- NOTE: annoyingly, HT.fromList uses (==) for equality
callGraphFromList :: [(Id, [Id])] -> IO CallGraph
callGraphFromList cls = do
    cg <- HT.new eq hash
    sequence_ [ HT.insert cg id ids | (id,ids) <- cls ]
    return (CG cg)

-- | reproduces the callgraph 
duplicateCallGraph :: CallGraph -> IO CallGraph
duplicateCallGraph cg = callGraphToList cg >>= callGraphFromList

-- | turns a normal call graph into a standard one
denormCallGraph :: NormCallGraph -> CallGraph
denormCallGraph (NCG cg) = CG cg

----------------------------------------
-- call graph generation

cgProg :: Prog -> IO CallGraph
cgProg (Prog ms) = do
    let ds  = concatMap moduleDecs ms
	lbs = [ lb | (ValDec _ lb) <- ds ]
    cg <- HT.new eq hash
    cgLetBnds (top,[],(CG cg)) lbs
    return (CG cg)
  where
    top = anonId "TOP!"

cgLetBnds :: Conf -> [LetBnd] -> IO LVs
cgLetBnds = multiple cgLetBnd

-- Add initial (empty) entries for the bound variables.
-- This is necessary in case those definition contain no function calls.
cgLetBnd :: Conf -> LetBnd -> IO LVs
cgLetBnd (c,lvs,cg) lb = case lb of
    LetBnd _ i e        -> updateCallGraph cg (i,[]) >> f i e
    LetBndAnn _ i _ _ e -> updateCallGraph cg (i,[]) >> f i e
  where 
    f i e = cgExp (i,lvs,cg) e
    
cgExp :: Conf -> Exp -> IO LVs
cgExp conf@(c,lvs,cg) e = case e of
    VarExp  id   -- this var. refers to a lambda-bound variable
	       | idStr id `elem` idStrs lvs -> return lvs
		 -- this is a call
	       | otherwise -> do updateCallGraph cg (c,[id])
				 return lvs
    ConExp  id -> return lvs
    LitExp  l  -> return lvs
    AppExp  s e1 e2 -> do lvs' <- cgExp conf e1
			  cgExp (c,lvs',cg) e2
    AbsExp  s i e   -> let lvs' = i : lvs in cgExp (c,lvs',cg) e
    LetExp  s lbs e -> do lvs' <- cgExp conf e
			  cgLetBnds (c,lvs',cg) lbs
    CaseExp s es ms -> do lvs' <- cgExps conf es
			  cgMatches (c,lvs',cg) ms

cgExps = multiple cgExp

cgMatch :: Conf -> Match -> IO LVs
cgMatch conf@(c,lvs,cg) (Match ps e) = do
    let ids  = patsIds ps
	lvs' = ids ++ lvs
    cgExp (c,lvs',cg) e

cgMatches = multiple cgMatch


patIds :: Pat -> [Id]
patIds (VarPat id) = [id]
patIds (LitPat _ ) = []
patIds (ConPat _ id ps) = id : patsIds ps
patIds (AnnPat _ id _) = [id]

patsIds :: [Pat] -> [Id]
patsIds ps = concatMap patIds ps

--------------------------------------------------------------------------------

-- | builds the transitive closure of the graph, returning a new normalised 
-- graph
normaliseCallGraph :: CallGraph -> IO NormCallGraph
normaliseCallGraph cg0 = do
    cg@(CG kg)  <- duplicateCallGraph cg0
    cls <- callGraphToList cg
    let (cs,_) = unzip cls
    mapM_ (proc cg) cs
    return (NCG kg)
  where
    -- Finds all the functions called (transitively) from c
    -- and updates the call graph with this information.
    proc :: CallGraph -> Id -> IO ()
    proc cg@(CG kg) c = do cs <- trans [] c
			   updateCallGraph cg (c,cs)
      where
        trans cs c = do
	    cs1 <- callees c
	    let cs2 = nubIds cs1
		cs3 = filter (`notElem`cs) cs2
	    if null cs3
	      then -- fixed point
		   return cs
	      else do cs4 <- thread (cs3++cs) cs2
		      return (nubIds cs4)
	  where
	    thread cs []     = return cs
	    thread cs (d:ds) = do
		cs1 <- trans cs d
		let cs2 = filter (`notElem`cs) (nubIds cs1)
		if null cs2 
		  then -- fixed point
		       return cs
		  else thread (cs2++cs) ds
  
	callees c = do 
	    mcs <- HT.lookup kg c
	    return $ case mcs of
			Nothing -> []
			Just cs -> cs


--------------------------------------------------------------------------------

-- | Finds strongly connected components in call graph, topologically sorted.
callGraphSCCs :: CallGraph -> IO [SCC]
callGraphSCCs cg = do
    cls <- callGraphToList cg
    let cls' = [ (f,f',fs') | (f,fs) <- cls, let f'  = idStr f,
					     let fs' = map idStr fs ]
	sccs = Gr.stronglyConnComp cls'
    return (map fromSCC sccs)
  where
    fromSCC (Gr.AcyclicSCC v) = [v]
    fromSCC (Gr.CyclicSCC vs) = vs

instance Show v => Show (Gr.SCC v) where
    show (Gr.AcyclicSCC v) = "AcyclicSCC " ++ show v
    show (Gr.CyclicSCC vs) = "CyclicSCC " ++ show vs


--------------------------------------------------------------------------------
-- Some miscellaneous queries/operations on call graphs.

-- | returns a list of all the let-bound variables represented in the CallGraph
callGraphVars :: CallGraph -> IO [Id]
callGraphVars cg = do
    cls <- callGraphToList cg
    return (map fst cls)

-- | given a normalised call graph, returns a list of all recursive variables
recursiveVars :: NormCallGraph -> IO [Id]
recursiveVars ncg = do
    let cg = denormCallGraph ncg
    ids <- callGraphVars cg
    rs <- mapM (varIsRecursive ncg) ids
    return [ id | (id,r) <- zip ids rs, r ]

-- given a normalised call graph, determines whether let-bound variable id is
-- recursive or not
varIsRecursive :: NormCallGraph -> Id -> IO Bool
varIsRecursive (NCG cg) id = do
    mcs <- HT.lookup cg id
    return $ case mcs of 
		Nothing -> False
		Just cs -> any (idStr id ==) (idStrs cs)
    
