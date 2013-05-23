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
-- This module defines the the translation from external AST with 
-- regular exp type/pattern extension to external AST in Standard Haskell 98 
--
--------------------------------------------------------------------------------


-- In Xhaskell program, all occurances of Prelude.() is treated as the empty word.

module X.XTrans where

import AST.Internal as I
import AST.Common 
import AST.Exports
import AST.SrcInfo
import X.REOpts 
import X.IAST
import X.ISubtype
import X.RESubtype
import X.XResult
import Core.InfResult
import Core.Constraint
import Core.Types as C
import Core.Name
import Misc
import Misc.Print
import Misc.Error
import Misc.Output.ANSI
import Misc.ErrorMsg
import Monad

type TEnv = [(IdStr,I.Type)]

type TheImports = [(IdStr, C.Type)]

data REState = REState { num     :: Int
                       , hImports :: TheImports
                       , srcinfo :: [SrcInfo]
                       , xImports :: TheImports
                       , exports :: [InfResult]
		       , wishlist :: [Wish]
                       }

data RS a = RS (REState -> XResult (REState,a))

instance Monad RS where
    -- return :: a -> RS a
    return a = RS (\st -> return (st, a))

    -- (>>=) :: RS a -> (a -> RS b) -> RS b
    (RS a) >>= f = RS (\st -> do (st', a') <- a st
			         let RS b = f a'
		                 b st')

    fail str = RS (\st -> XFailure [])

-- basic combinators (for lifting values into the monad)
(|>) :: Monad m => m (a -> b) -> m a -> m b
f |>  m = f >>= \g -> m >>= \r -> return (g $! r)

(||>) :: Monad m => (a -> b) -> m a -> m b
f ||> m = m >>= \r -> return (f $! r)


newSrcLoc :: RS SrcInfo
newSrcLoc = RS (\st -> let n = num st
                           p = hImports st
                           l = srcinfo st
                           i = xImports st
                           r = exports st
		           wl = wishlist st
                       in return ((REState (n+1) p l i r wl), (SrcInfo n "*ANON*" (-1) (-1) (-1))))

getHImports :: RS TheImports
getHImports = RS (\st -> let p = hImports st
                         in return (st, p))

setHImports :: TheImports -> RS ()
setHImports p = RS (\st -> let n = num st 
                               l = srcinfo st
                               i = xImports st
                               r = exports st
                               w = wishlist st
                           in return ((REState n p l i r w), ()))

addSrcInfo :: SrcInfo -> RS ()
addSrcInfo l = RS (\st -> let n = num st
                              p = hImports st
                              ls = srcinfo st
                              i = xImports st
                              r = exports st
                              w = wishlist st
                          in return ((REState n p (l:ls) i r w), ())) 

addExport :: InfResult -> RS ()
addExport x = RS (\st -> let n = num st
		             p = hImports st
		             l = srcinfo st
                             i = xImports st
                             xs = exports st
                             w = wishlist st 
                         in return ((REState n p l i (x:xs) w), ()))

getXImports :: RS TheImports
getXImports = RS (\st -> let i = xImports st
		         in return (st, i))

addWishList :: [Wish] -> RS ()
addWishList w = RS (\st -> let n = num st 
		               p = hImports st
		               l = srcinfo st
		               i = xImports st
		               x = exports st
                               wl = wishlist st
		               w' = filter (\e -> not (elem e wl)) w
                           in return ((REState n p l i x (w'++wl)), ()))

cleanWishList :: RS ()
cleanWishList = RS (\st -> let n = num st 
		               p = hImports st
		               l = srcinfo st
		               i = xImports st
		               x = exports st
                               wl = wishlist st
                           in return ((REState n p l i x []), ()))

getWishList :: RS [Wish]
getWishList = RS (\st -> let wl = wishlist st
		         in return (st, wl))

initRS :: Int -> TheImports -> TheImports -> REState
initRS i himp ximp  = REState i himp [] ximp [] []

mkAnnErrRS :: Id -> RS a
mkAnnErrRS i = RS (\st -> XFailure [(AnnErr i)])

mkUnboundVarErrRS :: Id -> RS a
mkUnboundVarErrRS i = RS (\st -> XFailure [(UnboundVarErr i)])

mkFunExpErrRS :: Exp -> RS a
mkFunExpErrRS e = RS (\st -> XFailure [(FunExpErr e)])

mkUnboundConErrRS :: Id -> RS a
mkUnboundConErrRS i = RS (\st -> XFailure [(UnboundConErr i)])

mkSubtypeErrRS :: SrcInfo -> I.Type -> I.Type -> RS a
mkSubtypeErrRS s sub sup = RS (\st -> XFailure [(SubtypeErr s sub sup)])

mkNonExhaustiveErrRS :: SrcInfo -> I.Type -> I.Type -> RS a
mkNonExhaustiveErrRS s aty pty = RS (\st -> XFailure [(NonExhaustiveErr s aty pty)])
				  
runRS :: REState -> RS a -> XResult (REState,a)
runRS s (RS a) = a s

---------------------------- interface to Translation AST ----------------------------
instance AST (RS Exp) (RS Pat) where
--  eApp :: RS Exp -> RS Exp -> RS Exp
    eApp me1 me2 = do {
		       srcLoc <- newSrcLoc;
		       e1 <- me1;
		       e2 <- me2;
		       return (AppExp srcLoc e1 e2)
		     }	
--  eAbs :: RS Pat -> RS Exp -> RS Exp
    eAbs p m = do {
		   s <- newSrcLoc;
                   s' <- newSrcLoc;
                   e' <- eCase (eVar ("v"++(show $ srcLoc s'))) [(p,m)];
		   return (AbsExp s (mkId s' ("v"++(show $ srcLoc s'))) e')
		  }
--  eCase :: RS Exp -> [(RS Pat,RS Exp)] -> RS Exp
    eCase me clauses = do {
			     e <- me;
			     alts <- matches clauses;
			     srcLoc <- newSrcLoc;
			     return (CaseExp srcLoc [e] alts)
			    }
        where matches :: [(RS Pat,RS Exp)] -> RS [Match]
	      matches l = mapM match l
	      match :: (RS Pat, RS Exp) -> RS Match
	      match (mp,me) = do {
				  p <- mp;
				  e <- me;
				  srcLoc <- newSrcLoc;
				  return (Match [p] e) 
				 }
--  eVar :: String -> RS Exp
    eVar s = do { srcLoc <- newSrcLoc;
	          return (VarExp (mkId srcLoc s))
	        }
--  eStr :: String -> RS Exp
    eStr s = do { srcLoc <- newSrcLoc;
		  return (LitExp (StrLit srcLoc s))
		}
--  eInt :: Integer -> RS Exp
    eInt i = do { srcLoc <- newSrcLoc;
                  return (LitExp (IntegerLit srcLoc i (show i)))
                }
--  eCon :: String -> RS Exp
    eCon s = do { srcLoc <- newSrcLoc;
	          return (ConExp (mkId srcLoc s))
	        }
--  eTup :: [(RS Exp)] -> RS Exp
    eTup [e1, e2] = ((eCon "(,)") `eApp` e1) `eApp` e2
    eTup (e:es) = ((eCon "(,)") `eApp` e) `eApp` (eTup es)

--  eNil :: RS Exp
    eNil = eCon "[]"
--  eCons :: RS Exp -> RS Exp -> RS Exp
    eCons me mes = ((eCon "(:)") `eApp` me) `eApp` mes
--  eLet :: [(RS Pat,RS Exp)] -> RS Exp -> RS Exp
    eLet clauses me = do { 
			  lbs <- letbnds clauses;
			  e <- me;
			  s <- newSrcLoc;
			  return (LetExp s lbs e)
		         }
        where letbnds :: [(RS Pat,RS Exp)] -> RS [LetBnd]
	      letbnds l = mapM letbnd l
	      letbnd :: (RS Pat,RS Exp) -> RS LetBnd
	      letbnd (mp,me) = do {
                                  -- FIXME: though currently all uses of eLet
                                  -- is applied to var pattern, but we need to 
                                  -- handle other cases for future extensions.
			           (VarPat id) <- mp; 
			           e <- me;
			           s <- newSrcLoc;
			           return (LetBnd s id e)
			          }
--  eL :: RS Exp -> RS Exp
    eL me = (eCon "Left") `eApp` me
--  eR :: RS Exp -> RS Exp
    eR me = (eCon "Right") `eApp` me
--  ePair :: RS Exp -> RS Exp -> RS Exp
    ePair me1 me2 = eTup [me1,me2]
--  eJust :: RS Exp -> RS Exp
    eJust me = (eCon "Just") `eApp` me
--  eNothing :: RS Exp 
    eNothing = eCon "Nothing"
--  ePlus ::  RS Exp
    ePlus = eCon "(+)"
--  eUndefined :: RS Exp
    eUndefined = eCon "undefined"
--  eError :: RS Exp
    eError s = (eCon "error") `eApp` (eStr s)
--  pVar :: String -> RS Pat
    pVar s = do { 
	         srcLoc <- newSrcLoc;
	         return (VarPat (mkId srcLoc s))
	        }
--  pCon :: String -> [(RS Pat)] -> RS Pat
    pCon s mps = do {
		     srcLoc1 <- newSrcLoc;
		     srcLoc2 <- newSrcLoc;
		     ps <- mapM id mps;
		     return (ConPat srcLoc1 (mkId srcLoc2 s) ps)
		    }
--  pTup :: [(RS Pat)] -> RS Pat
    pTup mps = do {
		   s <- newSrcLoc;
		   ps <- mapM id mps;
                   s' <- newSrcLoc;
		   return (ConPat s (mkId s' "(,)") ps)
		  }
--  pInt :: Integer -> RS Pat
    pInt i = do {
                 srcLoc <- newSrcLoc;
                 return (LitPat (IntegerLit srcLoc i (show i)))
                }
--  pL :: RS Pat -> RS Pat
    pL mp = pCon "Left" [mp]
--  pR :: RS Pat -> RS Pat
    pR mp = pCon "Right" [mp]
--  pPair :: RS Pat -> RS Pat -> RS Pat
    pPair mp1 mp2 = pTup [mp1,mp2]
--  pCons :: RS Pat -> RS Pat -> RS Pat
    pCons mp1 mp2 = pCon "(:)" [mp1,mp2]
--  pNil :: RS Pat
    pNil = pCon "[]" []
--  pJust :: RS Pat -> RS Pat
    pJust mp = pCon "Just" [mp]
--  pNothing :: RS Pat
    pNothing = pCon "Nothing" []
--  pWildcard :: RS Pat
    pWildcard = pCon "_" []

---------------------------------- Specific Translation code ------------------------------------

xtrans :: Int -> [(IdStr, (C.Type,Constraint))] -> [(IdStr, (C.Type,Constraint))] -> [I.Dec] -> Prog -> XResult (REState, Prog)
xtrans i himp ximp impdecs prog = let htenv = map (\ (i,(t,c)) -> (i, t)) himp
                                      xtenv = map (\ (i,(t,c)) -> (i, t)) ximp
                                  in transProg i htenv xtenv prog

transProg :: Int -> TheImports -> TheImports -> Prog -> XResult (REState,Prog)
transProg i himp ximp p = runRS (initRS i himp ximp) (do {trProg p})

trProg :: Prog -> RS Prog
trProg (Prog ms) = Prog ||> (mapM transModule ms)

transModule :: Module -> RS Module
transModule (Module id exs ims decs Xmod) = 
-- assume no ML function in the module 
    do {
        tenv <- mkInitTEnv decs; -- build the initial type environments
        decs' <- transDecs decs tenv;
        return (Module id exs ims' decs' Xmod)
       }
    where 
    --                ims' = imports ++ ims
    ims' = ims
    imports | any (==idStr id) reImports = []
	    | otherwise = map mkImport reImports
    mkImport m = let id = mkId builtInSrcInfo m
	         in  Import id (Qual id) ImAll

reImports = []



----------------------------------------------------------------
-- conversion among Interal Types and Core Types              --
----------------------------------------------------------------
iType2cType :: I.Type -> C.Type
iType2cType (AppType _ t1 t2) = TApp (iType2cType t1) (iType2cType t2)
iType2cType (ConType cid) = 
    let n = idStr cid
        s = idSrcInfo cid
    in  TCon (Name (NameRef s n) n)
iType2cType (VarType vid) = 
    let n = idStr vid
        s = idSrcInfo vid
    in  TVar (mkRefVar n s n)

cType2iType :: C.Type -> RS I.Type
cType2iType (TApp t1 t2) = 
    do { s <- newSrcLoc;
         t1' <- cType2iType t1;
         t2' <- cType2iType t2;
         return $ AppType s t1' t2'
       }
cType2iType (TCon (Name ref str)) = 
    case ref of
    NameRef s o -> return $ ConType (mkId s str)
    _           -> -- the rest we don't know about the srcinfo
                   do s <- newSrcLoc;
                      return $ ConType (mkId s str)
cType2iType (TVar var) = 
    let (Name ref str) = varName var 
    in 
    case ref of
    NameRef s o -> return $ VarType (mkId s str)
    _           -> -- the rest we don't know about the srcinfo
                   do s <- newSrcLoc;
                      return $ VarType (mkId s str)

                   


----------------------------------------------------------------
-- mkInitTEnv converts reg exp function signatures,           --
-- data declarations and XHaskell imports                     --
-- into the initial type enviornment.                         --
-- At the same time, type informations are stored in          --
-- the state as HM inference result.                          --
-- No parametric data declaration now. because we do not      --
-- support polymorphism now.                                  --
----------------------------------------------------------------
mkInitTEnv :: [Dec] -> RS TEnv
mkInitTEnv [] = do { p <- getXImports;
                     mapM ( \(i,t) -> do {t' <- cType2iType t; return (i,t')}) p
                   }
--mkInitTEnv [] = return []
mkInitTEnv ((ValDec s (LetBndAnn s' id _ (TSchm _ t) _)):decs) = 
-- we currently do not care about the type context attached to function
    do { tenv <- mkInitTEnv decs;
         addExport (InfSuccess id [(iType2cType t)] trueConstraint);
         return (((idStr id),t):tenv)
       }
mkInitTEnv ((DataDec s (DataType tid []) cons):decs) =
    do { tenv <- mkInitTEnv decs;
	 tenv' <- pcons cons;
	 return (tenv'++tenv)
       }
    where pcons :: [Cons] -> RS TEnv
	  pcons [] = return []
	  pcons ((Cons s qids cnst (DataType cid tparas)):cons) = 
	      do { ty <- pparas tparas;
		   addExport (InfSuccess cid [(iType2cType ty)] trueConstraint );
		   tenv <- pcons cons;
		   return (((idStr cid),ty):tenv)
		 }
	  pparas :: [I.Type] -> RS I.Type
	  pparas [] = return (ConType tid)
	  pparas (x:xs) = do { s <- newSrcLoc;
                               s' <- newSrcLoc;
                               s'' <- newSrcLoc;
			       xs' <- pparas xs;
			       return (AppType s (AppType s' (ConType (mkId s'' "->")) x) xs')
			     }
mkInitTEnv (_:decs) = mkInitTEnv decs

------------------------------------------------------------
-- lookup the type of an id from the environment          --
------------------------------------------------------------

lookUp :: IdStr -> TEnv -> RS (Maybe I.Type)
lookUp id [] = return Nothing
lookUp id ((id',ty):tenv)  = if (id == id') 
                             then return (Just ty)
                             else lookUp id tenv

------------------------------------------------------------
-- lookup the type of an id from the xImports              --
------------------------------------------------------------

lookUp' :: IdStr -> TheImports -> RS (Maybe I.Type)
lookUp' id [] = return Nothing
lookUp' id ((id',ty):tenv)  = if (id == id') 
                             then do ty' <- cType2iType ty
                                     return (Just ty')
                             else lookUp' id tenv



------------------------------------------------------------
-- transDecs :                                            --
-- Translate declarations.                                --
------------------------------------------------------------
transDecs :: [Dec] -> TEnv -> RS [Dec] 
transDecs [] _ = return []
transDecs (dec:decs) tenv = 
    case dec of
    -- assumption: all toplevel xhaskell letbnds must be annotated.
    ValDec s letb@(LetBndAnn _ _ _ (TSchm ctxt t) _)
        -> do { addSrcInfo (getSrcInfo dec);
                letb' <- transLetBndAnn tenv letb;
                decs' <- transDecs decs tenv;
                return ((ValDec s letb'):decs')
              }
    ValDec s letb@(LetBnd _ id _) ->  mkAnnErrRS id
    DataDec s (DataType id []) cons -- we currently do not accept parametric datatype
        -> do { addSrcInfo (getSrcInfo dec);
                cons' <- transCons cons;
		decs' <- transDecs decs tenv;
		return ((DataDec s (DataType id []) cons'):decs')
              }
        where transCons :: [Cons] -> RS [Cons]
              transCons [] = return []
              transCons ((Cons s ids cnst dt):cons) = do { dt' <- transDataType dt;
                                                           cons' <- transCons cons;
                                                           return ((Cons s ids cnst dt'):cons')
                                                         }
              transDataType :: DataType -> RS DataType
              transDataType (DataType id ts) = do { ts' <- mapM re2ht ts;
                                                    return (DataType id ts') 
                                                  }
    _ -> do { addSrcInfo (getSrcInfo dec);
              decs' <- transDecs decs tenv;
              return (dec:decs')
            }


--------------------------------------------------------------------------------
-- transLetBndAnn : Translate the top level annotated let-bind, AKA Let rule  --
-- It takes type enivronment and a letbnd, returns a translated letbnd        --
--------------------------------------------------------------------------------
transLetBndAnn :: TEnv -> LetBnd -> RS LetBnd
transLetBndAnn tenv (LetBndAnn s1 id1 at (TSchm ctxt t) (AbsExp s2 id2 (LetExp s3 letbnds e))) =
{-
transValDec tenv ity oty (ValDec src (defs@((Def id pat rhs wh):_))) 
    | (isHaskell ity) = -- it must be haskell pattern matching on the top most level, 
                        -- currently limit to single parameter K
	do {
	    letdecs <- transHDefs tenv ity oty defs 1;
	    letexp <- do {
			  srcLoc <- newSrcLoc;
			  return (LetExp src letdecs (VarExp (mkId srcLoc "p_1")))
			 };
	    wl <- getWishList;
	    decs <- wishListToDecs wl;
	    cleanWishList;
            srcLoc1 <- newSrcLoc;
            srcLoc2 <- newSrcLoc;
	    return (ValDec srcLoc1 [Def id [(VarPat (mkId srcLoc2 "v_in"))] (RHS1 letexp) decs])
	}
    | otherwise =  -- regular expression pattern
-}
    case t of
    AppType _ (AppType _ (ConType cid) it) ot 
        | (idStr cid) == "->" -> 
            do {
	        _ <- exhaustCheck s1 tenv it letbnds;
                t' <- re2ht t;
                letbnds' <- transLetBnds tenv it it ot letbnds;
	        wl <- getWishList;
	        wletbnds <- wishListToLetBnds wl;
	        cleanWishList;
                return (LetBndAnn s1 id1 at (TSchm ctxt t') (AbsExp s2 id2 (LetExp s3 (wletbnds++letbnds') e)))
               }
    _ -> mkAnnErrRS id1
transLetBndAnn tenv (LetBndAnn s1 id1 at (TSchm ctxt t) (AbsExp s2 id2 e)) = 
    do { s3 <- newSrcLoc;
         s4 <- newSrcLoc;
         s5 <- newSrcLoc;
         e' <- eVar "x$2";
         transLetBndAnn tenv (LetBndAnn s1 id1 at (TSchm ctxt t) (AbsExp s2 id2 (LetExp s3 [LetBnd s4 (mkId s5 "x$2") e] e')))
       }
transLetBndAnn tenv e = bug (show e)

isHaskell (ConType _) = True
isHaskell _ = False

----------------------------------------------------------------------------
--  wishListToLetBnds :                                                   --
--       turns a list of wishes into a list of letbnds                    --
----------------------------------------------------------------------------
wishListToLetBnds :: [Wish] -> RS [LetBnd]
wishListToLetBnds [] = return []
wishListToLetBnds (w:ws) = 
    do { lb <- wishToLetBnd w;
         lbs <- wishListToLetBnds ws;
         return (lb:lbs)
       }

wishToLetBnd :: Wish -> RS LetBnd
wishToLetBnd w = do  
                 let n = case w of
		         (To r) -> ("tn"++(reToFuncName r))
		         (From r) -> ("fn"++(reToFuncName r))
	         e <- wishComesTrue w
	         s1 <- newSrcLoc
	         s2 <- newSrcLoc
	         return (LetBnd s1 (mkId s2 n) e)


----------------------------------------------------------------------------
-- Check whether the patterns are exhaustive w.r.t to the input type      --
----------------------------------------------------------------------------
exhaustCheck :: SrcInfo -> TEnv -> I.Type -> [LetBnd] -> RS Exp
exhaustCheck s tenv t lbs = do 
    ptys <- mapM (\ (LetBnd _ _ (CaseExp _ _ [ (Match [pat] _) , _ ])) -> do stript tenv pat
                 ) lbs
    pu <- buildUnion ptys -- union of all pattern ann types
    r2 <- type2re pu
    r1 <- type2re t
    case (runST initState (ucast r1 r2)) of 
      Just (_, e) -> e
      Nothing -> mkNonExhaustiveErrRS s t pu
    where buildUnion :: [I.Type] -> RS I.Type
	  buildUnion [x] = return x
	  buildUnion (x:xs) = do 
			      s1 <- newSrcLoc;
                              s2 <- newSrcLoc;
                              s3 <- newSrcLoc;
			      xs' <- buildUnion xs
			      return (AppType s1 (AppType s2 (ConType (mkId s3 "|")) x) xs')


----------------------------------------------------------------------------
-- transLetBnds ::  Type Env -> Input type -> Left-Over type ->               --
--               Output type -> Defs -> Pattern Counter -> RS Decs        --
-- translate a list of Defs which are regular expression pattern          --
-- clauses                                                                --
----------------------------------------------------------------------------
transLetBnds :: TEnv -> I.Type -> I.Type -> I.Type -> [LetBnd] -> RS [LetBnd]
-- no more pattern
transLetBnds _ _ _ _ [] = return [] 
transLetBnds tenv ity lty oty ((LetBnd s1 id1 (CaseExp s2 [e] [(Match [pat] body), (Match _ other)])):lbs) = 
    do {
        -- pattern inference
	-- pattern annotated type
        aty <- stript tenv pat;       
	-- precise pattern type = leftover type \cap pattern annotated type     
        pty <- intersect lty aty;     
	-- new leftover type
        lty' <- difference lty pty;   
--        lty' <- return lty;
	-- infer a local type environment
        tenv' <- inferPat tenv pty pat;    
	-- constructing the Haskell pattern
        pat' <- stripv pat;
	-- infer R gammar_i. We take the initial tenv to support K pattern           
        gty <- mkRGammar (tenv++tenv') pat';  
        -- body inference/translation
        (bty,bexp) <- transExp (tenv'++tenv) body; --fixme: need to ensure that ++ is safe for tenv union
	rg <- type2re gty;
	ri <- type2re ity;
	case (checkLeq rg ri) of
	False -> do {
		     caseExp <- (eCase ((mkDCast (getSrcInfo pat) pty ity) `eApp` (return e))
				 [ 
				  ( (pCon "Just" [pVar "pv"])
{- case exp is used instead of let exp, because I haven't fixed the eLet
--				    , (eLet [((stripv pat)
--					     ,((mkUCast (getSrcInfo pat) pty gty) `eApp` (eVar "pv")))]
--				       ((mkUCast (getSrcInfo body) bty oty) `eApp` (return bexp)))
-}
                                    , (eCase ((mkUCast (getSrcInfo pat) pty gty) `eApp` (eVar "pv"))
                                       [((stripv pat), ((mkUCast (getSrcInfo body) bty oty) `eApp` (return bexp)))])
                                  )
				  , 
				  ( (pCon "Nothing" []), (return other)) 
				 ]
				);
		     lbs' <- transLetBnds tenv ity lty' oty lbs; -- translate the remaining patterns.
		     return ((LetBnd s1 id1 caseExp):lbs')
		     }
	True -> do { -- when rgammar is a subtype of input type, we combine dcast and the value distro
		    caseExp <- (eCase ((mkDCast (getSrcInfo pat) gty ity) `eApp` (return e))
				[ 
				 ( (pCon "Just" [stripv pat])
				   , ((mkUCast (getSrcInfo body) bty oty) `eApp` (return bexp)))
				 , 
				 ( (pCon "Nothing" []), (return other) )
				]
			       );
		     lbs' <- transLetBnds tenv ity lty' oty lbs; -- translate the remaining patterns.
		     return ((LetBnd s1 id1 caseExp):lbs')
		   }
       }


{-
-- Currently, we use data to introduce regular literal, which makes
-- mixing regular expression pattern and haskell pattern difficult.
-- This is quick fix to enable Haskell pattern at the topmost level.
-- it will be obselete when we have a proper declaration for label.
-- and all datatypes are just haskell types.
transHDefs :: TEnv -> Type -> Type -> [Def] -> Int -> RS [Dec]
-- no more pattern
transHDefs _ _ _ [] c = 
    do { patDec <- (patdec (pVar ("p_"++(show c))) ((eCon "error") `eApp` (eStr "NEP")));
	 return [patDec]
       }
-- there is at lest one pattern
transHDefs tenv ity oty ((Def _ [(ConPat _ cid [pat])] (rhs@(RHS1 body)) wh):defs) c = do
	-- pattern inference
        res <- lookUp cid tenv
        case res of
	  Just (ArrType _ ity' t') -> do
              aty <- stript tenv pat
	      pty <- intersect ity' aty
	      tenv' <- inferPat tenv pty pat
	      pat' <- stripv pat;
	      gty <- mkRGammar (tenv++tenv') pat'
	      (bty,bexp) <- transExp (tenv'++tenv) body
	      patDec <- patdec (pVar ("p_"++(show c))) 
			(eCase ((eAbs (pCon (idStr cid) [(pVar "v_in'")])
				 ((mkDCast (getSrcInfo pat) pty ity') `eApp` (eVar "v_in'")))
				`eApp` (eVar "v_in"))
			 [ -- the first pattern clause 
			   ((pCon "Just" [pVar ("pv_"++(show c))])
			   , (eLet [((stripv pat)
				    ,((mkUCast (getSrcInfo pat) pty gty) `eApp` (eVar ("pv_"++(show c)))))]
			      ((mkUCast (getSrcInfo body) bty oty) `eApp` (return bexp))))
			 , -- the second pattern clause
			   ( (pCon "Nothing" []), (eVar ("p_"++(show (c+1)))) )
			 ])
	      defs' <- transHDefs tenv ity oty defs (c+1)
	      return (patDec:defs')
	  Nothing -> mkUnboundConErrRS cid


-----------------------------------------------------------------------
-- transRHS :: Type Env -> RHS -> RS (Infered Type, Translated Exp)  --
-- translate the RHS                                                 --
-----------------------------------------------------------------------
transRHS :: TEnv -> RHS -> RS (Type,Exp)
transRHS tenv (RHS1 exp) = transExp tenv exp 
-}


-----------------------------------------------------------------------
-- translate the expression                                          --
-----------------------------------------------------------------------
transExp :: TEnv -> Exp -> RS (I.Type,Exp)
transExp tenv (AppExp s1 (AppExp s2 (ConExp cid) e1) e2) 
    | idStr cid == "(,)" = do {
                               (t1,e1') <- transExp tenv e1;
                               (t2,e2') <- transExp tenv e2;
                               s3 <- newSrcLoc;
                               s4 <- newSrcLoc;
                               s5 <- newSrcLoc;
                               return ((AppType s3 (AppType s4 (ConType (mkId s5 "(,)")) t1) t2)
                                      ,(AppExp s1 (AppExp s2 (ConExp cid) e1') e2'))
                              }
transExp tenv (ConExp cid)
    | idStr cid == "()" = do { s <- newSrcLoc;
                               e <- eNil;
                               return ((ConType (mkId s "()")),e)
                             }
    | idStr cid == "Prelude.()" = do { s <- newSrcLoc;
                               e <- eNil;
                               return ((ConType (mkId s "Prelude.()")),e)
                             }
    | otherwise = do { res <- lookUp (idStr cid) tenv;
                       case res of 
                       Just t -> return (t,(ConExp cid))
                       Nothing -> mkUnboundConErrRS cid
                     }

transExp tenv (LitExp lit@(StrLit _ _)) = do 
        srcLoc <- newSrcLoc
        let t = ConType (mkId srcLoc "String")
        return (t,(LitExp lit))
transExp tenv (VarExp id) = 
    do { res <- lookUp (idStr id) tenv;
         himp <- getHImports;
         res' <- lookUp' (idStr id) himp;
         case (res `mplus` res') of
         Just t ->  return (t,(VarExp id))
         Nothing -> mkUnboundVarErrRS id
       }
transExp tenv (AppExp _ e1 e2) = 
    do { (t1,e1') <- transExp tenv e1;
         case t1 of
         (AppType _ (AppType _ (ConType cid) t1') t1'') | idStr cid == "->" -> 
            do { (t2,e2') <- transExp tenv e2;
                 b <- checkHImports e1';  
		 -- check whether it is a hImports function
                 if b then do { e <- (return e1') `eApp` (return e2');
                                return ((substitute (instantiate t1' t2) t1''),e)
                              }   
                 else do { e <- (return e1') `eApp` ((mkUCast (getSrcInfo e2) t2 t1') `eApp` (return e2'));
			   return (t1'', e) 
                         }
	       }
	 _ -> mkFunExpErrRS e1
       }
    where checkHImports :: Exp -> RS Bool
          checkHImports (VarExp id) = 
	     do { p <- getHImports;
		  res <- lookUp' (idStr id) p;
		  case res of 
		  Just _ -> return True
		  _ -> return False
		}
          checkHImports _ = return False
	  instantiate :: I.Type -> I.Type -> [(String,I.Type)]
	  instantiate (VarType id) t = [((idStr id), t)]
          instantiate (AppType _ t1 t1') (AppType _ t2 t2') = 
              (instantiate t1 t2)++(instantiate t1' t2')
          instantiate (ConType id1) (ConType id2) | idStr id1 == idStr id2 = []
	  instantiate t1 t2 = bug ("TransExp : unable to instantiate type "
				   ++(pretty t1)
				   ++" against "
				   ++(pretty t2))
	  substitute :: [(String,I.Type)] -> I.Type -> I.Type
          substitute s (VarType id) = case (lookup (idStr id) s) of
				      Just t -> t
				      Nothing -> (VarType id)
          substitute s (ConType id) = ConType id
          substitute s (AppType si t1 t2) = AppType si (substitute s t1) (substitute s t2)

transExp tenv e = bug (show e)

--------------------------------------------------------------
-- type2re : convert type into regular expression           --
--------------------------------------------------------------
type2re :: I.Type -> RS RE
type2re (AppType s1 (AppType s2 (ConType cid) t1) t2) 
    | idStr cid == "|" = do { r1 <- type2re t1;
                              r2 <- type2re t2;
                              return (Or r1 r2)
                            }
    | idStr cid == "(,)" = do { r1 <- type2re t1;
                              r2 <- type2re t2;
                              return (Pr r1 r2)
                            }
type2re (AppType s1 (ConType cid) t1) 
    | idStr cid == "*" = do { r1 <- type2re t1;
                              return (St r1)
                            }
type2re (ConType cid) 
    | idStr cid == "()" = return Em
    | idStr cid == "Prelude.()" = return Em -- in xhaskell, unit is treated as Em
    | idStr cid == "{}" = return Ph
    | otherwise = return (Lab (idStr cid))
type2re t = bug ("type2re fail: " ++ (pretty t)++" can't be converted to regular expression") 

--------------------------------------------------------------
-- re2type : convert regular exlression to type             --
--------------------------------------------------------------
re2type :: RE -> RS I.Type
re2type (St re) = do {
		      s1 <- newSrcLoc;
                      s2 <- newSrcLoc;
		      ty <- re2type re;
		      return (AppType s1 (ConType (mkId s2 "*")) ty)
		     }
re2type (Or re re') = do {
			  s1 <- newSrcLoc;
                          s2 <- newSrcLoc;
                          s3 <- newSrcLoc;
			  ty <- re2type re;
			  ty' <- re2type re';
			  return (AppType s1 (AppType s2 (ConType (mkId s3 "|")) ty) ty')
			 }
re2type (Pr re re') = do {
			  s1 <- newSrcLoc;
                          s2 <- newSrcLoc;
                          s3 <- newSrcLoc;
			  ty <- re2type re;
			  ty' <- re2type re';
			  return (AppType s1 (AppType s2 (ConType (mkId s3 "(,)")) ty) ty')
			 }
re2type (Lab s) = do {
		      srcLoc <- newSrcLoc;
		      return (ConType (mkId srcLoc s))
		     }
re2type Em = do {
                 srcLoc <- newSrcLoc;
                 return (ConType (mkId srcLoc "()"))
                }
re2type Ph = do {
                 srcLoc <- newSrcLoc;
                 return (ConType (mkId srcLoc "{}"))
                }



--------------------------- Interface to RE Subtype Proof System ---------------------------------
-- Note: t1 <: t2
mkDCast :: SrcInfo -> I.Type -> I.Type -> RS Exp
mkDCast s t1 (AppType s' (ConType cid) t2) | idStr cid == "[]" = 
                                               mkDCast s t1 (AppType s' (ConType (mkId (idSrcInfo cid) "*")) t2)
mkDCast s (AppType s' (ConType cid) t1) t2 | idStr cid == "[]" = 
                                               mkDCast s (AppType s' (ConType (mkId (idSrcInfo cid) "*")) t1) t2
mkDCast s t1 t2 = 
    do {
        r1 <- type2re t1;
        r2 <- type2re t2;
        case (runST initState (dcast r1 r2)) of 
              Just (st, e) -> do
                           let w = wishList st
	                   addWishList w
	                   e
	      Nothing -> mkSubtypeErrRS s t1 t2
       }
{-
mkDCast s t1 t2 =
    do {
        srcLoc <- newSrcLoc;
        return (VarExp (mkId srcLoc ("dcast"++(pretty t1)++"<:"++(pretty t2))))
       }
-}


-- Note: t1 <: t2
mkUCast :: SrcInfo -> I.Type -> I.Type -> RS Exp
mkUCast s t1 (AppType s' (ConType cid) t2) | idStr cid == "[]" = 
                                               mkUCast s t1 (AppType s' (ConType (mkId (idSrcInfo cid) "*")) t2)
mkUCast s (AppType s' (ConType cid) t1) t2 | idStr cid == "[]" = 
                                               mkUCast s (AppType s' (ConType (mkId (idSrcInfo cid) "*")) t1) t2
mkUCast s t1 t2 =
    do {
        r1 <- type2re t1;
        r2 <- type2re t2;
        case (runST initState (ucast r1 r2)) of 
              Just (st, e) -> do
                           let w = wishList st
	                   addWishList w
	                   e
	      Nothing -> mkSubtypeErrRS s t1 t2
       }

{-
mkUCast s t1 t2 =
    do {
        srcLoc <- newSrcLoc;
        return (VarExp (mkId srcLoc ("ucast"++(pretty t1)++"<:"++(pretty t2))))
       }
-}

----------------------------- Wrapper for Regexp Operations ----------------
intersect :: I.Type -> I.Type -> RS I.Type
intersect t1 t2 = do {
		      r1 <- type2re t1;
		      r2 <- type2re t2;
		      re2type (isect r1 r2);
		     }

difference :: I.Type -> I.Type -> RS I.Type
difference t1 t2 = do {
		       r1 <- type2re t1;
		       r2 <- type2re t2;
		       re2type (diff r1 r2);
		      }

leftbreak :: I.Type -> I.Type -> I.Type -> RS I.Type
leftbreak t1 t2 t3 = do {
                         r1 <- type2re t1;
                         r2 <- type2re t2;
                         r3 <- type2re t3;
                         re2type (lbreak_nd r1 r2 r3);
                        }      

rightbreak :: I.Type -> I.Type -> I.Type -> RS I.Type
rightbreak t1 t2 t3 = do {
                          r1 <- type2re t1;
                          r2 <- type2re t2;
                          r3 <- type2re t3;
                          re2type (rbreak_nd r1 r2 r3);
                         }

----------------------------- Pattern Inference ---------------------------\
-- inferPat:  tenv,r,p|- tenv 
-- because of k pattern, we need to add init tenv
inferPat :: TEnv -> I.Type -> Pat -> RS TEnv
inferPat _ t (AnnPat _ id t') = do { t'' <- intersect t t';
                                     return [((idStr id),t'')]
				   }	
inferPat tenv t (ConPat s cid [p1,p2]) 
    | idStr cid == "(,)" = do { t1 <- stript tenv p1;
				t2 <- stript tenv p2;
				t1' <- leftbreak t t1 t2;
				t2' <- rightbreak t t1 t2;
				tenv1 <- inferPat tenv t1' p1;
				tenv2 <- inferPat tenv t2' p2;
				return (tenv1++tenv2)
			      }
inferPat tenv t (ConPat _ cid pats) = do { res <- lookUp (idStr cid) tenv;
					   case res of
					   Just kty -> inferParas kty pats
					   Nothing -> mkUnboundConErrRS cid
					 }
    where inferParas :: I.Type -> [Pat] -> RS TEnv -- though we say Type, but it could be only ArrType or ConType
	  inferParas t' [] = do { _ <- mkUCast (getSrcInfo t') t' t; -- the final type must be a subtype of input type.
				  return [];
				}
	  inferParas (AppType _ (AppType _ (ConType cid') t1) t2) (pat:pats) 
              | idStr cid' == "->" = 
                  do { tenv' <- inferPat tenv t1 pat;
		       tenv'' <- inferParas t2 pats;
		       return (tenv'++tenv'')
		     }



mkRGammar :: TEnv -> Pat -> RS I.Type
mkRGammar tenv (VarPat id) = do {
				 res <- lookUp (idStr id) tenv;
				 case res of 
				 Just t -> return t
				 Nothing -> mkUnboundVarErrRS id
				}	
mkRGammar tenv (ConPat _ cid [p1,p2]) 
    | idStr cid == "(,)" = do {
                               t1 <- mkRGammar tenv p1;
                               t2 <- mkRGammar tenv p2;
                               s1 <- newSrcLoc;
                               s2 <- newSrcLoc;
                               s3 <- newSrcLoc;
                               return (AppType s1 (AppType s2 (ConType (mkId s3 "(,)")) t1) t2)
                              }
mkRGammar tenv (ConPat _ cid pats) = do { res <- lookUp (idStr cid) tenv;
					  case res of 
					  Just kty -> mkRGammarParas kty pats;
					  Nothing -> mkUnboundConErrRS cid
					}
    where mkRGammarParas :: I.Type -> [Pat] -> RS I.Type
	  mkRGammarParas t [] = return t
	  mkRGammarParas (AppType _ (AppType _ (ConType cid') t1) t2) (pat:pats)
              | idStr cid' == "->" = 
          -- make sure annotated type is exact to the declared type
	      do { t1' <- mkRGammar tenv pat;
                   r1' <- type2re t1';
                   r1 <- type2re t1;
                   if (checkEqual r1' r1) 
                   then mkRGammarParas t2 pats 
                   else bug ("mkRGammar: Constructor pattern argument is annotated with "
                             ++ (pretty t1') 
                             ++ " which is different from the declaration " 
                             ++ (pretty t1))
		 }



----------------------------- Auxilary Functions --------------------------
-- fixme : currently we ONLY support binary tuples
stripv :: Pat -> RS Pat 
stripv (AnnPat _ id _) = return (VarPat id)
stripv (ConPat si cid pats) = do { pats' <- mapM stripv pats;
				   return (ConPat si cid pats')
				 }	


-- takes in an extra parameter TEnv due to K patterns
stript :: TEnv -> I.Pat -> RS I.Type
stript _ (AnnPat _ id ty) = return ty
stript tenv (ConPat _ cid [p1,p2]) 
    | idStr cid == "(,)" = do {
                               s1 <- newSrcLoc;
                               s2 <- newSrcLoc;
                               s3 <- newSrcLoc;
                               t1 <- stript tenv p1;
                               t2 <- stript tenv p2;
                               return (AppType s1 (AppType s2 (ConType (mkId s3 "(,)")) t1) t2)
			      }
stript tenv (ConPat _ cid pats) = 
    do { res <- lookUp (idStr cid) tenv;
	 case res of 
	 Just kty -> striptParas kty pats;
	 Nothing -> mkUnboundConErrRS cid
       }
    where striptParas :: I.Type -> [Pat] -> RS I.Type
	  striptParas t [] = return t;
	  striptParas (AppType _ (AppType _ (ConType cid') t1) t2) (pat:pats) 
              | idStr cid' == "->" = 
                  do { t1' <- stript tenv pat;
		  -- make sure annotated type is exact to the declared type
                       r1' <- type2re t1';
                       r1 <- type2re t1;
                       if (checkLeq r1' r1) 
                       then striptParas t2 pats
                       else bug ("stript: Constructor pattern argument is annotated with "
                                 ++ (pretty t1') 
                                 ++ " which is different from the declaration " 
                                 ++ (pretty t1) ++ "\n" ++ (pretty tenv))
		     }

stript tenv p = bug (show p)

checkEqual :: RE -> RE -> Bool
checkEqual r1 r2 =  
    case (runST initState (ucast r1 r2)) of 
      Just (_, (e::(RS Exp))) -> case (runST initState (ucast r2 r1)) of
                     Just (_, (e::(RS Exp))) -> True
                     Nothing -> False
      Nothing -> False

checkLeq :: RE -> RE -> Bool
checkLeq r1 r2 =  
    case (runST initState (ucast r1 r2)) of 
      Just (_, (e::(RS Exp))) -> case (runST initState (ucast r2 r1)) of
                     Just (_, (e::(RS Exp))) -> True
                     Nothing -> False
      Nothing -> False



--------------------------------------------------------------------------------
-- Translation of type: from regular expression type to type in target language
--------------------------------------------------------------------------------
-- {| r* |}   -> [ {| r |} ]
-- {| (r,r') |} -> ({| r |}, {| r' |})
-- {| (r|r') |} -> (Or {| r |} {| r' |})
-- {| l |} -> l
-- {| Em |} -> []
-- {| [r] |} -> [ {| r |} ]
--------------------------------------------------------------------------------
-- convert type to haskell type
re2ht :: I.Type -> RS I.Type
re2ht (AppType s1 (AppType s2 (ConType id) t1) t2)
    | (idStr id) == "|" = do { t1' <- re2ht t1;
                               t2' <- re2ht t2;
                               s3 <- newSrcLoc;
                               return (AppType s1 (AppType s2 (ConType (mkId s3 "Either")) t1') t2')
                             }
    | (idStr id) == "(,)" = do { t1' <- re2ht t1;
                                 t2' <- re2ht t2;
                                 s3 <- newSrcLoc;
                                 return (AppType s1 (AppType s2 (ConType (mkId s3 "(,)")) t1') t2')
                               }
    | (idStr id) == "->" = do { t1' <- re2ht t1;
                                t2' <- re2ht t2;
                                s3 <- newSrcLoc;
                                return (AppType s1 (AppType s2 (ConType (mkId s3 "->")) t1') t2')
                              }
re2ht (AppType s (ConType id) t) 
    | (idStr id) == "*" = do { t' <- re2ht t;
                               s' <- newSrcLoc;
                               return (AppType s (ConType (mkId s' "[]")) t');
                             }
    | (idStr id) == "[]" = do { t' <- re2ht t;
                                s' <- newSrcLoc;
                                return (AppType s (ConType (mkId s' "[]")) t');
                              }
re2ht (ConType id) | (idStr id) == "()" = do { s1 <- newSrcLoc;
                                               s2 <- newSrcLoc;
                                               s3 <- newSrcLoc;
                                               return (AppType s1 (ConType (mkId s2 "[]")) (ConType (mkId s3 "()")))
                                             } -- FIXME: "()" is overloaded
re2ht r = return r



xerror2error :: SrcTextData -> XError -> Error
xerror2error sd (AnnErr id) = 
    let hdr = ["Unannotated Function '" ++ (idStr id)++ "' from:"]
	s   = printHLLocs sd [(getSrcLoc id)]
	src = printSpec s
	src'= map (\s -> if null s then " " else s) (lines src)
	msg = errorMsg id (hdr ++ src')
    in mkError id msg
xerror2error sd (UnboundVarErr id) = 
    let hdr = ["Unbound Variable '"++ (idStr id) ++ "' from:"]
	s   = printHLLocs sd [(getSrcLoc id)]
	src = printSpec s
	src'= map (\s -> if null s then " " else s) (lines src)
	msg = errorMsg id (hdr ++ src')
    in mkError id msg
xerror2error sd (UnboundConErr id) = 
    let hdr = ["Unbound Constructor '"++ (idStr id) ++ "' from:"]
	s   = printHLLocs sd [(getSrcLoc id)]
	src = printSpec s
	src'= map (\s -> if null s then " " else s) (lines src)
	msg = errorMsg id (hdr ++ src')
    in mkError id msg
xerror2error sd (FunExpErr e) = 
    let hdr = ["XHaskell Type Error", "Expression at:"]
	s   = printHLLocs sd [(getSrcLoc e)]
	src = printSpec s 
	src'= map (\s -> if null s then " " else s) (lines src)
	foot= ["is used as a function, but it does not have function type."]
	msg = errorMsg e (hdr ++ src'++ foot)
    in mkError e msg
xerror2error sd (SubtypeErr s t1 t2) =
    let hdr = ["XHaskell Type Error", "Expression at:"]
	ss  = printHLLocs sd [(getSrcLoc s)]
	src = printSpec ss
	src'= map (\s -> if null s then " " else s) (lines src)
	body= [("has an inferred type "++(pretty t1)++" which is not a subtype of "++(pretty t2))]
        msg = errorMsg s (hdr ++ src' ++ body)
    in mkError s msg
xerror2error sd (NonExhaustiveErr s at pt) =
    let hdr = ["XHaskell Type Error", "Patterns at:"]
	ss  = printHLLocs sd [(getSrcLoc s)]
	src = printSpec ss
	src'= map (\s -> if null s then " " else s) (lines src)
	body= [("has an inferred type "++(pretty pt)++" which is not exhaustive with repect to input type "++(pretty at))]
	msg = errorMsg s (hdr ++ src' ++body)
    in mkError s msg
