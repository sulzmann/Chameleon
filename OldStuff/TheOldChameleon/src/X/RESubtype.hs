------------------------------------------------------
-- The regular expression subtyping proof system    --
------------------------------------------------------
module X.RESubtype 
    ( runST, initState, ucast, dcast, nucast, ndcast, tnorm, tmono, tmono', Wish(..), wishComesTrue,reToFuncName, wishList
    ) where

import X.ISubtype
import X.IAST
import X.REOpts
import Misc.ErrorMsg
import Misc

data State = State { counter :: Int
                   , context :: [((RE,RE),String)]
		   , wishlist :: [Wish] -- added for code size reduction
                   }

data ST a = ST (State -> Maybe (State,a))

runST :: State -> ST a -> Maybe (State,a)
runST s (ST a) = a s

initState = State 1 [] []

instance Monad ST where
    -- return :: a -> ST a
    return a = ST (\l -> return (l, a))

    -- (>>=) :: ST a -> (a -> ST b) -> ST b
    (ST f) >>= g = ST (\s -> do (s',a) <- f s
		                let (ST e) = g a
                                e s')
    fail str = ST (\s -> Nothing)
instance Env ST (RE,RE) where
--  newName :: ST String
    newName = ST (\st -> let cnt = counter st
                             ctxt = context st
		             wl = wishlist st
                         in return (State (cnt + 1) ctxt wl, "f"++(show cnt) ))
--  check :: (RE,RE) -> ST (Maybe String)
    check rs = ST (\st -> let ctxt = context st
                          in return (st, (lookup rs ctxt)))
--  add :: ((RE,RE),String) -> ST ()
    add (rs,name) = ST (\st -> let cnt = counter st
                                   ctxt = context st
			           wl  = wishlist st
                               in return (State cnt ((rs,name):ctxt) wl, ()))
--  del :: ((RE,RE),String) -> ST ()
    del (rs,name) = ST (\st -> let cnt = counter st
                                   ctxt = context st
			           wl = wishlist st
                               in return (State cnt (filter (rs,name) ctxt) wl, ()))
                    where filter _ [] = []
                          filter e (e':es) | e == e'   = es
                                           | otherwise = e':(filter e es)

--  wishT :: (RE,RE) -> ST ()
    wishT (r,_) = ST (\st -> let cnt = counter st
	                         ctxt = context st
                                 wl = wishlist st
	                     in if (elem (To r) wl) 
	                        then return (st,())
	                        else return (State cnt ctxt ((To r):wl), ()))
--  wishF :: (RE,RE) -> ST ()
    wishF (_,r) = ST (\st -> let cnt = counter st
	                         ctxt = context st
                                 wl = wishlist st
	                     in if (elem (From r) wl) 
	                        then return (st,())
	                        else return (State cnt ctxt ((From r):wl), ()))

instance UCast RE RE where
    ucast r1 r2 | (r1 == r2) = return (eAbs (pVar "u") (eVar "u")) -- build an identity function
{- old style : norm functions are constructed in place.
		| otherwise  = -- return (eVar ((show r1)++(show r2)))
                               let (n1,tn1,_) = tnorm r1
                                   (n2,_,fn2) = tnorm r2
                               in 
                                  do { 
				       nu <- nucast n1 n2;
                                       return (eAbs (pVar "u") (fn2 `eApp` (nu `eApp` (tn1 `eApp` (eVar "u")))))
                                     }
-}
		| otherwise  = let (n1,tn1) = mkToNorm r1
				   (n2,fn2) = mkFromNorm r2
			       in do {
				       nu <- nucast n1 n2;
				       wishT (r1,undefined); -- make a wish for toNorm r1
				       wishF (undefined,r2); -- make a wsih for fromNorm r2
				       return (eAbs (pVar "u") (fn2 `eApp` (nu `eApp` (tn1 `eApp` (eVar "u")))))
				     }	

instance NUCast RE RE where
    nucast Ph n = return eUndefined -- (eError ("u"++(show Ph)++"->"++(show n)))       -- phi <: r is always true, but the proof term is not needed. 
    nucast (Or Em n1') (Or Em n2') = 
	do {
	   nu <- nucast n1' n2';
	   return (eAbs (pVar "nu")  
		   (eCase (eVar "nu")
		    [ ((pL pNil), (eL eNil))
		    , ((pR (pVar "z")), (eR (nu `eApp` (eVar "z"))))
		    ]));
           }
    nucast (Or (m1@(Pr (Lab l1) r1)) n1') (Or (m2@(Pr (Lab l2) r2)) n2') | l1 == l2 =
        do {  
	   fname <- check (m1,m2);
	   case fname of
	   Just name -> return (eVar name) {- if Hyp applies; -}
	   Nothing -> do {
			  name <- newName;
			  add ((m1,m2),name);
			  u <- ucast r1 r2;
			  del ((m1,m2),name);
			  nu <- nucast n1' n2';
			  return (eLet [( (pVar name)
					, (eAbs (pVar "nu")
					   (eCase (eVar "nu")
					    [ ((pL (pPair (pVar "l") (pVar "r1"))), 
					       (eL (ePair (eVar "l") (u `eApp` (eVar "r1")))))
					    , ((pR (pVar "n1'")), (eR (nu `eApp` (eVar "n1'"))))
					    ])
					  )
					)]
				  (eVar name))
			 }
           }
    nucast (Or m1 n1') (Or m2 n2') | m2 < m1 =
	do { 
	   nu <- nucast (Or m1 n1') n2';
	   return (eAbs (pVar "nu") (eR (nu `eApp` (eVar "nu"))))
           } 
    nucast n1 n2 = fail ""


instance DCast RE RE where
    dcast r1 r2 | (r1 == r2) = return (eAbs (pVar "d") (eJust (eVar "d")))
{- old style
                | otherwise  = let (n1,_,fn1) = tnorm r1
                                   (n2,tn2,_) = tnorm r2
                               in do {
                                      nd <- ndcast n1 n2;
                                      return (eAbs (pVar "d") 
				              (eCase (nd `eApp` (tn2 `eApp` (eVar "d")))
				               [ ((pJust (pVar "n1")), (eJust (fn1 `eApp` (eVar "n1"))))
				               , (pNothing, eNothing)]))
                                     }
-}
		| otherwise  = let (n1,fn1) = mkFromNorm r1
				   (n2,tn2) = mkToNorm r2
			       in do {
                                      nd <- ndcast n1 n2;
				      wishF (undefined,r1); -- make a wsih for fromNorm r1
				      wishT (r2,undefined); -- make a wish for toNorm r2
                                      return (eAbs (pVar "d") 
				              (eCase (nd `eApp` (tn2 `eApp` (eVar "d")))
				               [ ((pJust (pVar "n1")), (eJust (fn1 `eApp` (eVar "n1"))))
				               , (pNothing, eNothing)]))

				     }	


instance NDCast RE RE where
--  ndcast Ph _ = return eUndefined       
--  phi <: r is always true, I thought the proof term is not needed. 
--  but, it can't be undefined, consider ndcast (()|{}) ((()|(A,())|{}) = 
--  nd = \x -> case x of L [] -> L []
--                       R v -> nd' v
--  where nd' = ndcast {} ((A,())|{})
--  if nd' is undefined, in case when we apply nd to value R (L (A,[])), run-time error is raised, which 
--  is not expected. Therefore, we should let nd' = \_-> Nothing
--  it seems that it does not apply to ucast
    ndcast Ph _ = return (eAbs pWildcard eNothing)
    ndcast (Or Em n1') (Or Em n2') =
	do { nd <- ndcast n1' n2';
             return (eAbs (pVar "nd1") 
		     (eCase (eVar "nd1")
		      [ ((pL pNil), (eJust (eL eNil)))
		      , ((pR (pVar "n2'")), (eCase (nd `eApp` (eVar "n2'"))
					     [ ((pJust (pVar "n1'")), (eJust (eR (eVar "n1'"))))
					     , (pNothing, eNothing)
					     ]))
		      ]))
	   }
    ndcast (Or (m1@(Pr (Lab l1) r1)) n1') (Or (m2@(Pr (Lab l2) r2)) n2') | l1 == l2 =
        do { 
	    fname <- check (m1,m2);
	    case fname of
	    Just name -> return (eVar name) -- if Hyp applies; 
	    Nothing -> do { -- otherwise		       
			    name <- newName;
			    add ((m1,m2),name);
			    d <- dcast r1 r2;
			    del ((m1,m2),name);
			    nd <- ndcast n1' n2';
			    return (eLet [( (pVar name)
					  , (eAbs (pVar "nd2")
					     (eCase (eVar "nd2")
					      [ ((pL (pPair (pVar "l") (pVar "r2"))),
						 (eCase (d `eApp` (eVar "r2"))
						  [ ((pJust (pVar "r1")), ((eJust (eL (ePair (eVar "l") (eVar "r1"))))))
						  , (pNothing, eNothing)]))
					      , ((pR (pVar "n2'")),
						 (eCase (nd `eApp` (eVar "n2'"))
						  [ ((pJust (pVar "n1'")), (eJust (eR (eVar "n1'"))))
						  , (pNothing, eNothing)]))
					      ])))
					 ]
				    (eVar name))
			  }
	   }
    ndcast (Or m1 n1') (Or m2 n2') | m2 < m1 =
        do { nd <- ndcast (Or m1 n1') n2';
             return (eAbs (pVar "nd3")
		     (eCase (eVar "nd3")
		      [ ((pL pWildcard), eNothing)
		      , ((pR (pVar "n2'")), (nd `eApp` (eVar "n2'")))]))
           }
    ndcast n1 n2 = fail ""



instance Norm RE where
--  tnorm :: (AST e p) => t -> (t,e,e)
    tnorm r = let m = mono r
                  s = sort_ m
                  n = lnf s
                  (tm,fm) = tmono r
                  (ts,fs) = tsort m 
		  (tl,fl) = tlnf s 
	      in (n,
                  (eAbs (pVar "tn") (tl `eApp` (ts `eApp` (tm `eApp` (eVar "tn"))))),
	          (eAbs (pVar "fn") (fm `eApp` (fs `eApp` (fl `eApp` (eVar "fn")))))
                 )
-- Maybe we should abstract this too.
tmono :: (AST e p) => RE -> (e,e)
-- tmono r = (eVar ("tmono"++(show r)), eVar ("fmono"++(show r)))
tmono r = let (tm,fm) = tmono' r 
          in 
          case (emptyword r) of
          True -> -- RE0 : the language contains empty word.
                  let (te,fe) = temptyword r
                  in ((eAbs (pVar "tm")
                       (eCase (te `eApp` (eVar "tm"))
                        [ ((pJust pNil), (eL eNil))
                        , (pNothing, (eR (tm `eApp` (eVar "tm")))) ]))
                     ,(eAbs (pVar "fm")
                       (eCase (eVar "fm")
                        [ ((pL pNil), (fe `eApp` eNil))
                        , ((pR (pVar "rs")), (fm `eApp` (eVar "rs"))) ])))
          False -> (tm,fm) -- RE1 : the language does not contain empty word.

tmono' :: (AST e p) => RE -> (e,e)
tmono' Ph = (eUndefined,eUndefined) -- ((eError ("tm'"++(show Ph))), (eError ("fm'"++(show Ph))))  -- It will not be evaluated.
tmono' Em = (eUndefined,eUndefined) -- ((eError ("tm'"++(show Em))), (eError ("fm'"++(show Em)))) 
--short cut
tmono' (Lab l) = ((eAbs (pVar "l") (eL (ePair (eVar "l") eNil)))
                 ,(eAbs (pVar "x") (eCase (eVar "x")
                                    [ ((pL (pPair (pVar "l") pNil)), (eVar "l")) 
				    ])))
--                                    , ((pR pWildcard), {- (eError ("fm'"++(show (Lab l)))) -} eUndefined )])))
tmono' (St r) | emptyword r = let (te,fe) = temptyword r
				  (tm,fm) = tmono'' r (St r)
			      in ((eLet [((pVar "rec"),
					  (eAbs (pVar "x")
					   (eCase (eVar "x")
					    [((pCons (pVar "m") (pVar "ms")), 
					      (eCase (te `eApp` (eVar "m"))
					       [((pJust pNil), ((eVar "rec") `eApp` (eVar "ms")))
					       ,(pNothing, (tm `eApp` (ePair (eVar "m") (eVar "ms"))))]))])))]
				   (eVar "rec"))
				 , (eAbs (pVar "x")
				    (eCase (fm `eApp` (eVar "x"))
				     [((pPair (pVar "m") (pVar "ms")), (eCons (eVar "m") (eVar "ms")))])))
	      | otherwise = let (tm,fm) = tmono'' r (St r)
			    in ((eAbs (pVar "x")
				 (eCase (eVar "x")
				  [((pCons (pVar "m") (pVar "ms")), (tm `eApp` (ePair (eVar "m") (eVar "ms"))))
				  ]))
-- short cut
--				  ,(pWildcard, {- (eError ("fm'"++(show (St r)))) -} eUndefined)]))
			       ,(eAbs (pVar "x")
				 (eCase (fm `eApp` (eVar "x"))
				  [((pPair (pVar "m") (pVar "ms")), (eCons (eVar "m") (eVar "ms")))])))
tmono' (Or r1 r2) = let rs1 = mono' r1
                        rs2 = mono' r2
                        (tm1,fm1) = tmono' r1
                        (tm2,fm2) = tmono' r2
                        (ta,fa) = tappend rs1 rs2
                    in ((eAbs (pVar "x")
                         (eCase (eVar "x")
                          [((pL (pVar "r1")), (ta `eApp` (eL (tm1 `eApp` (eVar "r1")))))
                          ,((pR (pVar "r2")), (ta `eApp` (eR (tm2 `eApp` (eVar "r2")))))]))
                       ,(eAbs (pVar "x")
                         (eCase (fa `eApp` (eVar "x"))
                          [((pL (pVar "v")), (eL (fm1 `eApp` (eVar "v"))))
                          ,((pR (pVar "v")), (eR (fm2 `eApp` (eVar "v"))))])))
tmono' (Pr Ph r) = ({- (eError ("tm'"++(show (Pr Ph r))))-}eUndefined,{-(eError ("fm'"++(show (Pr Ph r))))-}eUndefined)
tmono' (Pr Em r) = let (tm,fm) = tmono' r
                   in ((eAbs (pPair pNil (pVar "r")) (tm `eApp` (eVar "r")))
                      ,(eAbs (pVar "r") (ePair eNil (fm `eApp` (eVar "r")))))
tmono' (Pr (Lab l) r1) = ((eAbs (pVar "x") (eL (eVar "x")))
                         ,(eAbs (pL (pVar "x")) (eVar "x")))
tmono' (Pr (Pr r1 r2) r3) = let (tm,fm) = tmono' (Pr r1 (Pr r2 r3)) 
                            in ((eAbs (pPair (pPair (pVar "r1") (pVar "r2")) (pVar "r3"))
                                 (tm `eApp` (ePair (eVar "r1") (ePair (eVar "r2") (eVar "r3")))))
                               ,(eAbs (pVar "x")
                                 (eCase (fm `eApp` (eVar "x"))
                                  [ ((pPair (pVar "r1") (pPair (pVar "r2") (pVar "r3")))
                                    ,(ePair (ePair (eVar "r1") (eVar "r2")) (eVar "r3"))) ])))
tmono' (Pr (Or r1 r2) r3) = let (tm,fm) = tmono' (Or (Pr r1 r3) (Pr r2 r3))
                            in ((eAbs (pPair (pVar "r12") (pVar "r3"))
                                 (eCase (eVar "r12")
                                  [((pL (pVar "r1")), (tm `eApp` (eL (ePair (eVar "r1") (eVar "r3")))))
                                  ,((pR (pVar "r2")), (tm `eApp` (eR (ePair (eVar "r2") (eVar "r3")))))]))
                               ,(eAbs (pVar "x")
                                 (eCase (fm `eApp` (eVar "x"))
                                  [((pL (pPair (pVar "r1") (pVar "r3"))), (ePair (eL (eVar "r1")) (eVar "r3")))
                                  ,((pR (pPair (pVar "r2") (pVar "r3"))), (ePair (eR (eVar "r2")) (eVar "r3")))])))
tmono' (Pr (St r1) r2) = let rs1 = mono'' (St r1) r2
                             rs2 = mono' r2
                             (tm1,fm1) = tmono'' (St r1) r2
                             (tm2,fm2) = tmono' r2
                             (ta,fa) = tappend rs1 rs2
                         in ((eAbs (pVar "x")
                              (eCase (eVar "x")
                               [ ((pPair pNil (pVar "r2")), (ta `eApp` (eR (tm2 `eApp` (eVar "r2")))))
                               , ((pPair (pCons (pVar "r1") (pVar "r1s")) (pVar "r2")), (ta `eApp` (eL (tm1 `eApp` (ePair (eCons (eVar "r1") (eVar "r1s")) (eVar "r2"))))))]))
                            ,(eAbs (pVar "x")
                              (eCase (fa `eApp` (eVar "x"))
                               [ ((pL (pVar "v")), (eCase (fm1 `eApp` (eVar "v"))
                                                    [((pPair (pVar "r1s") (pVar "r2")), (ePair (eVar "r1s") (eVar "r2")))]))
                               , ((pR (pVar "v")), (eCase (fm2 `eApp` (eVar "v"))
                                                    [((pVar "r2"), (ePair eNil (eVar "r2")))])) ])))

tmono'' :: (AST e p) => RE -> RE -> (e,e)
tmono'' Em r = ({-(eError ("tm''"++(show Em)++","++(show r)))-}eUndefined,{-(eError ("fm''"++(show Em)++","++(show r)))-}eUndefined)
tmono'' (Lab l) r = ((eAbs (pPair (pVar "l") (pVar "r"))
                      (eL (ePair (eVar "l") (eVar "r"))))
                    ,(eAbs (pL (pPair (pVar "l") (pVar "r")))
                      (ePair (eVar "l") (eVar "r"))))
tmono'' (St r1) r2 | emptyword r1 = let (te,fe) = temptyword r1
					(tm,fm) = tmono'' r1 (Pr (St r1) r2)
				    in ((eLet [((pVar "rec"),
						(eAbs (pPair (pVar "r1s") (pVar "r2"))
						 (eCase (eVar "r1s")
						  [ (pNil, {-(eError ("tm''"++(show (St r1))++","++(show r2)))-}eUndefined)
						  , ((pCons (pVar "r1") (pVar "r1s'"))
						    ,(eCase (te `eApp` (eVar "r1"))
						      [((pJust pNil), ((eVar "rec") `eApp` (ePair (eVar "r1s'") (eVar "r2"))))
						      ,(pNothing, (tm `eApp` (ePair (eVar "r1") (ePair (eVar "r1s'") (eVar "r2")))))]))])))]
					 (eVar "rec"))
				       ,(eAbs (pVar "x")
					 (eCase (fm `eApp` (eVar "x"))
					  [ ((pPair (pVar "r1") (pPair (pVar "r1s") (pVar "r2")))
					    ,(ePair (eCons (eVar "r1") (eVar "r1s")) (eVar "r2"))) ])))
		   | otherwise = let (tm,fm) = tmono'' r1 (Pr (St r1) r2)
				 in ((eAbs (pPair (pVar "r1s") (pVar "r2"))
				      (eCase (eVar "r1s")
				       [ (pNil, {-(eError ("tm''"++(show (St r1))++","++(show r2)))-}eUndefined)
				       , ((pCons (pVar "r1") (pVar "r1s'"))
					 ,(tm `eApp` (ePair (eVar "r1") (ePair (eVar "r1s'") (eVar "r2")))))]))
				    ,(eAbs (pVar "x")
				      (eCase (fm `eApp` (eVar "x"))
				       [ ((pPair (pVar "r1") (pPair (pVar "r1s") (pVar "r2")))
					 ,(ePair (eCons (eVar "r1") (eVar "r1s")) (eVar "r2"))) ])))
tmono'' (Or r1 r2) r3 = let rs' = mono'' r1 r3
                            rs'' = mono'' r2 r3
                            (tm,fm) = tmono'' r1 r3
                            (tm',fm') = tmono'' r2 r3
                            (ta,fa) = tappend rs' rs''
                        in ((eAbs (pPair (pVar "r12") (pVar "r3"))
                             (eCase (eVar "r12")
                              [ ((pL (pVar "r1")), (ta `eApp` (eL (tm `eApp` (ePair (eVar "r1") (eVar "r3"))))))
                              , ((pR (pVar "r2")), (ta `eApp` (eR (tm' `eApp` (ePair (eVar "r2") (eVar "r3"))))))]))
                           ,(eAbs (pVar "x")
                             (eCase (fa `eApp` (eVar "x"))
                              [ ((pL (pVar "v")), (eCase (fm `eApp` (eVar "v"))
                                                   [ ((pPair (pVar "r1") (pVar "r3"))
                                                     ,(ePair (eL (eVar "r1")) (eVar "r3"))) ]))
                              , ((pR (pVar "v")), (eCase (fm' `eApp` (eVar "v"))
                                                   [ ((pPair (pVar "r2") (pVar "r3"))
                                                     ,(ePair (eR (eVar "r2")) (eVar "r3"))) ])) ])))
tmono'' (Pr Em r1) r2 = let (tm,fm) = tmono'' r1 r2
                        in ((eAbs (pPair (pPair pNil (pVar "r1")) (pVar "r2")) 
                             (tm `eApp` (ePair (eVar "r1") (eVar "r2"))))
                           ,(eAbs (pVar "x")
                             (eCase (fm `eApp` (eVar "x"))
                              [((pPair (pVar "r1") (pVar "r2")),(ePair (ePair eNil (eVar "r1")) (eVar "r2")))])))
tmono'' (Pr (Lab l) r1) r2 = ((eAbs (pPair (pPair (pVar "l") (pVar "r1")) (pVar "r2"))
                               (eL (ePair (eVar "l") (ePair (eVar "r1") (eVar "r2")))))
                             ,(eAbs (pL (pPair (pVar "l") (pPair (pVar "r1") (pVar "r2"))))
                               (ePair (ePair (eVar "l") (eVar "r1")) (eVar "r2"))))
tmono'' (Pr (Pr r1 r2) r3) r4 = let (tm,fm) = tmono'' (Pr r1 (Pr r2 r3)) r4
                                in ((eAbs (pPair (pPair (pPair (pVar "r1") (pVar "r2")) (pVar "r3")) (pVar "r4"))
                                     (tm `eApp` (ePair (ePair (eVar "r1") (ePair (eVar "r2") (eVar "r3"))) (eVar "r4"))))
                                   ,(eAbs (pVar "x")
--                                     (eCase (eVar "x") 
--                                     possibily a bug!!!
                                     (eCase (fm `eApp` (eVar "x"))
                                      [ ((pPair (pPair (pVar "r1") (pPair (pVar "r2") (pVar "r3"))) (pVar "r4"))
                                        ,(ePair (ePair (ePair (eVar "r1") (eVar "r2")) (eVar "r3")) (eVar "r4")))])))
tmono'' (Pr (Or r1 r2) r3) r4 = let (tm,fm) = tmono'' (Or (Pr r1 r3) (Pr r2 r3)) r4
                                in ((eAbs (pPair (pPair (pVar "r12") (pVar "r3")) (pVar "r4"))
                                     (eCase (eVar "r12")
                                      [ ((pL (pVar "r1")), (tm `eApp` (ePair (eL (ePair (eVar "r1") (eVar "r3"))) (eVar "r4"))))
                                      , ((pR (pVar "r2")), (tm `eApp` (ePair (eR (ePair (eVar "r2") (eVar "r3"))) (eVar "r4"))))]))
                                   ,(eAbs (pVar "x")
                                     (eCase (fm `eApp` (eVar "x"))
                                      [ ((pPair (pL (pPair (pVar "r1") (pVar "r3"))) (pVar "r4"))
                                        ,(ePair (ePair (eL (eVar "r1")) (eVar "r3")) (eVar "r4")))
                                      , ((pPair (pR (pPair (pVar "r2") (pVar "r3"))) (pVar "r4"))
                                        ,(ePair (ePair (eR (eVar "r2")) (eVar "r3")) (eVar "r4")))
                                      ])))
tmono'' (Pr (St r1) r2) r3 = let rs = mono'' (St r1) (Pr r2 r3)
                                 rs' = mono'' r2 r3
                                 (tm,fm) = tmono'' (St r1) (Pr r2 r3)
                                 (tm',fm') = tmono'' r2 r3
                                 (ta,fa) = tappend rs rs'
                             in ((eAbs (pPair (pPair (pVar "r1s") (pVar "r2")) (pVar "r3"))
                                  (eCase (eVar "r1s")
                                   [ (pNil, (ta `eApp` (eR (tm' `eApp` (ePair (eVar "r2") (eVar "r3"))))))
                                   , ((pCons (pVar "r1") (pVar "r1s'")), (ta `eApp` (eL (tm `eApp` (ePair (eVar "r1s") (ePair (eVar "r2") (eVar "r3")))))))
                                   ]))
                                ,(eAbs (pVar "x")
                                  (eCase (fa `eApp` (eVar "x"))
                                   [ ((pL (pVar "v")), (eCase (fm `eApp` (eVar "v"))
                                                        [ ((pPair (pVar "r1s") (pPair (pVar "r2") (pVar "r3")))
                                                          ,(ePair (ePair (eVar "r1s") (eVar "r2")) (eVar "r3"))) ]))
                                   , ((pR (pVar "v")), (eCase (fm' `eApp` (eVar "v"))
                                                        [ ((pPair (pVar "r2") (pVar "r3"))
                                                          ,(ePair (ePair eNil (eVar "r2")) (eVar "r3"))) ]))])))

-- assumption: value under the first list must be indexed with L, value under the 2nd list must be indexed with R
tappend :: (AST e p) => [RE] -> [RE] -> (e,e)
tappend [] ms = ( (eAbs (pVar "ta")
                   (eCase (eVar "ta")
                    [ ((pL pWildcard), {-(eError ("ta"++"[],"++(show ms)))-}eUndefined)
                    , ((pR (pVar "m")), (eVar "m"))]))
                , (eAbs (pVar "fa") (eR (eVar "fa")))
                )
-- short cut
tappend ms [] = ( eAbs (pVar "ta")
		  (eCase (eVar "ta")
		   [ ((pL (pL (pVar "m"))), (eL (eVar "m"))) ])
		, eAbs (pVar "fa")
		  (eCase (eVar "fa")
		   [ ((pL (pVar "m")), (eL (eL (eVar "m")))) ])
		)
-- short cut 
tappend [m] ms = ( eAbs (pVar "ta") 
		   (eCase (eVar "ta")
		    [ ((pL (pL (pVar "m"))), (eL (eVar "m")))
		    , ((pR (pVar "m")), (eR (eVar "m")))
		    ])
		 , eAbs (pVar "fa") 
		   (eCase (eVar "fa")
		    [ ((pL (pVar "m")), (eL (eL (eVar "m"))))
		    , ((pR (pVar "m")), (eR (eVar "m")))
		    ])
		 )
tappend (m:ms) ms' = let (ta,fa) = tappend ms ms'
                     in ((eAbs (pVar "ta")
                          (eCase (eVar "ta")
                           [ ((pL (pL (pVar "m"))), (eL (eVar "m")))
                           , ((pL (pR (pVar "m"))), (eR (ta `eApp` (eL (eVar "m")))))
                           , ((pR (pVar "m")), (eR (ta `eApp` (eR (eVar "m")))))]))
                        ,(eAbs (pVar "fa")
                          (eCase (eVar "fa")
                           [ ((pL (pVar "m")), (eL (eL (eVar "m"))))
                           , ((pR (pVar "m")), (eCase (fa `eApp` (eVar "m"))
                                                [ ((pL (pVar "m'")), (eL (eR (eVar "m'"))))
                                                , ((pR (pVar "m'")), (eR (eVar "m'"))) ]))
                           ]))
                        )
-- precondition: r must possess empty word
temptyword :: (AST e p) => RE -> (e,e)
temptyword Em = ((eAbs pNil (eJust eNil)),(eAbs pNil eNil))
temptyword (St r) = if (emptyword r) 
                    then let (te,fe) = temptyword r
                         in
                         ((eLet [((pVar "rec")
                                 ,(eAbs (pVar "te") 
                                   (eCase (eVar "te")
                                    [(pNil, (eJust eNil))
                                    ,((pCons (pVar "y") (pVar "ys"))
                                     ,(eCase (te `eApp` (eVar "y"))
                                       [((pJust pNil), ((eVar "rec") `eApp` (eVar "ys")))
                                       ,(pNothing, eNothing)]))
                                    ])))]
                           (eVar "rec"))
                         ,(eAbs pNil eNil))
                    else ((eAbs (pVar "te")
                           (eCase (eVar "te")
                            [(pNil, (eJust eNil))
                            ,((pCons (pVar "y") (pVar "ys")), eNothing)]))
                         ,(eAbs pNil eNil))
temptyword (Pr r1 r2) = let (te1,fe1) = temptyword r1
                            (te2,fe2) = temptyword r2
                        in ((eAbs (pPair (pVar "r1") (pVar "r2"))
                             (eCase (te1 `eApp` (eVar "r1"))
                              [((pJust pNil), (te2 `eApp` (eVar "r2")))
                              ,(pNothing, eNothing)]))
                           ,(eAbs pNil (ePair (fe1 `eApp` eNil) (fe2 `eApp` eNil))))
temptyword (Or r1 r2) = if (emptyword r1)
                        then let (te1,fe1) = temptyword r1
                             in if (emptyword r2)
                                then let (te2,fe2) = temptyword r2
                                     in ((eAbs (pVar "r12")
                                          (eCase (eVar "r12")
                                           [((pL (pVar "r1")), (te1 `eApp` (eVar "r1")))
                                           ,((pR (pVar "r2")), (te2 `eApp` (eVar "r2")))]))
                                        ,(eAbs pNil (eL (fe1 `eApp` eNil))))
                                else ((eAbs (pVar "x")
                                       (eCase (eVar "x")
                                        [ ((pL (pVar "r1")), (te1 `eApp` (eVar "r1")))
                                        , ((pR (pVar "r2")), eNothing) ]))
                                     ,(eAbs pNil (eL (fe1 `eApp` eNil))))
                        else let (te2,fe2) = temptyword r2
                             in ((eAbs (pVar "te")
                                  (eCase (eVar "te")
                                   [ ((pL (pVar "v")), eNothing)
                                   , ((pR (pVar "v")), (te2 `eApp` (eVar "v"))) ]))
                                ,(eAbs pNil (eR (fe2 `eApp` eNil))))

tsort :: (AST e p) => [RE] -> (e,e)
tsort [] = ({-(eError ("ts []"))-}eUndefined, {-(eError ("fs []"))-}eUndefined)
-- short cut
tsort [m] = (eAbs (pVar "ts") (eVar "ts"), eAbs (pVar "fs") (eVar "fs"))
tsort (m:ms) = let (ti,fi) = tinsert m (sort_ ms)
                   (ts,fs) = tsort ms
               in ((eAbs (pVar "ts")
                    (eCase (eVar "ts")
                     [ ((pL (pVar "m")), (ti `eApp` (eL (eVar "m"))))
                     , ((pR (pVar "m")), (ti `eApp` (eR (ts `eApp` (eVar "m")))))]))
                  ,(eAbs (pVar "fs")
                    (eCase (fi `eApp` (eVar "fs"))
                     [ ((pL (pVar "m")), (eL (eVar "m")))
                     , ((pR (pVar "m")), (eR (fs `eApp` (eVar "m"))))]))
                  )
-- Proof term invariant : undelying value of m must be indexed with L; values of ms are indexed with R
tinsert :: (AST e p) => RE -> [RE] -> (e,e)
-- short cut
tinsert m [] = ((eAbs (pVar "ti") (eCase (eVar "ti") 
		                  [ ((pL (pVar "v")), (eL (eVar "v"))) 
				  ]))
--                                    , (pWildcard, {-(eError ("ti"++(show m)++",[]"))-}eUndefined) ]))
               ,(eAbs (pVar "fi") (eCase (eVar "fi") 
		                  [ ((pL (pVar "v")), (eL (eVar "v")))
				  ]))
--                                    , (pWildcard,  {-(eError ("fi"++(show m)++",[]"))-}eUndefined) ]))
	       )
tinsert (Pr l r) ((Pr l' r'):ms) | l == l' = let (tg,fg) = tsmerge r r'
					     in ((eAbs (pVar "ti")
                                                  (eCase (eVar "ti")
                                                   [ ((pL (pPair (pVar "l") (pVar "v"))), (eL (ePair (eVar "l") (tg `eApp` (eL (eVar "v"))))))
                                                   , ((pR (pL (pPair (pVar "l") (pVar "v")))), (eL (ePair (eVar "l") (tg `eApp` (eR (eVar "v"))))))
                                                   , ((pR (pR (pVar "m"))), (eR (eVar "m")))
                                                   ]))
                                                ,(eAbs (pVar "fi")
                                                  (eCase (eVar "fi")
                                                   [ ((pL (pPair (pVar "l") (pVar "v"))), (eCase (fg `eApp` (eVar "v"))
                                                                                           [ ((pL (pVar "v'")), (eL (ePair (eVar "l") (eVar "v'"))))
											   , ((pR (pVar "v'")), (eR (eL (ePair (eVar "l") (eVar "v'"))))) ]))
                                                   , ((pR (pVar "m")), (eR (eR (eVar "m"))))]))
                                                )
				 | l < l' = ((eAbs (pVar "ti") (eVar "ti")),(eAbs (pVar "fi") (eVar "fi")))
				 | l > l' = let (ti,fi) = tinsert (Pr l r) ms
				            in ((eAbs (pVar "ti")
                                                 (eCase (eVar "ti")
                                                  [ ((pL (pVar "m")), (eR (ti `eApp` (eL (eVar "m")))))
                                                  , ((pR (pL (pVar "m"))), (eL (eVar "m")))
                                                  , ((pR (pR (pVar "m"))), (eR (ti `eApp` (eR (eVar "m")))))]))
                                               ,(eAbs (pVar "fi")
                                                 (eCase (eVar "fi")
                                                  [ ((pL (pVar "m")), (eR (eL (eVar "m"))))
                                                  , ((pR (pVar "m")), (eCase (fi `eApp` (eVar "m"))
                                                                       [ ((pL (pVar "m'")), (eL (eVar "m'")))
                                                                       , ((pR (pVar "m'")), (eR (eR (eVar "m'"))))]))]))
                                               ) 
tinsert m (m':ms) | m < m' = ((eAbs (pVar "ti") (eVar "ti")),(eAbs (pVar "fi") (eVar "fi")))
		  | otherwise = let (ti,fi) = tinsert m ms
				in ((eAbs (pVar "ti")
                                     (eCase (eVar "ti")
                                      [ ((pL (pVar "m")), (eR (ti `eApp` (eL (eVar "m")))))
                                      , ((pR (pL (pVar "m"))), (eL (eVar "m")))
                                      , ((pR (pR (pVar "m"))), (eR (ti `eApp` (eR (eVar "m")))))]))
                                   ,(eAbs (pVar "fi")
                                     (eCase (eVar "fi")
                                      [ ((pL (pVar "m")), (eR (eL (eVar "m"))))
                                      , ((pR (pVar "m")), (eCase (fi `eApp` (eVar "m"))
                                                           [ ((pL (pVar "m'")), (eL (eVar "m'")))
                                                           , ((pR (pVar "m'")), (eR (eR (eVar "m'"))))]))]))
                                   ) 

					    
tsmerge :: (AST e p) => RE -> RE -> (e,e)
tsmerge r1 r2 | r1 == r2 = ( -- tg
			    (eAbs (pVar "tg") 
			     (eCase (eVar "tg")
			      [ ((pL (pVar "v")), (eVar "v")), ((pR (pVar "v")), (eVar "v"))  ]))
			   , -- fg
			     (eAbs (pVar "fg") -- heuristically, we chose the left branch.
			      (eL (eVar "fg")))
			   )
	      | otherwise = case r2 of 
			    (Or r1' r2') -> 
				if (r1 == r1') 
				then ( (eAbs (pVar "tg")
					(eCase (eVar "tg")
					 [ ((pL (pVar "v")), (eL (eVar "v")))
					 , ((pR (pL (pVar "v"))), (eL (eVar "v")))
					 , ((pR (pR (pVar "v"))), (eR (eVar "v")))
					 ]))
				     , (eAbs (pVar "fg") 
					(eCase (eVar "fg")
					 [ ((pL (pVar "v")), (eL (eVar "v"))) -- heuristic
					 , ((pR (pVar "v")), (eR (eR (eVar "v"))))
					 ]))
				     )
				else (if (r1 > r1')
                                      then 
                                      let (tg,fg) = tsmerge r1 r2'
				      in ( (eAbs (pVar "tg") 
					    (eCase (eVar "tg")
					     [ ((pL (pVar "v")), (eR (tg `eApp` (eL (eVar "v")))))
					     , ((pR (pL (pVar "v"))), (eL (eVar "v")))
					     , ((pR (pR (pVar "v"))), (eR (tg `eApp` (eR (eVar "v")))))
					     ]))
					 , (eAbs (pVar "fg")
					    (eCase (eVar "fg")
					     [ ((pL (pVar "v")), (eR (eL (eVar "v"))))
					     , ((pR (pVar "v")), (eCase (fg `eApp` (eVar "v"))
								  [((pL (pVar "v'")), (eL (eVar "v'")))
								  ,((pR (pVar "v'")), (eR (eR (eVar "v'"))))]))
					     ]))
					 )
                                      else ( (eAbs (pVar "tg") (eVar "tg"))
                                           , (eAbs (pVar "fg") (eVar "fg"))
                                           )
                                      )
			    _ -> (if (r1 > r2)
                                  then ((eAbs (pVar "tg") (eCase (eVar "tg")
                                                           [ ((pL (pVar "v")), (eR (eVar "v")))
                                                           , ((pR (pVar "v")), (eL (eVar "v")))
                                                           ]))
                                       ,(eAbs (pVar "fg") (eCase (eVar "fg")
                                                           [ ((pL (pVar "v")), (eR (eVar "v")))
                                                           , ((pR (pVar "v")), (eL (eVar "v")))
                                                           ]))
                                       )
                                  else ( (eAbs (pVar "tg") (eVar "tg"))
				       , (eAbs (pVar "fg") (eVar "fg"))))

tlnf :: (AST e p) => [RE] -> (e,e)
tlnf m = ( (eAbs (pVar "tl") (eVar "tl"))
	 , (eAbs (pVar "fl") (eVar "fl")))




data Wish = To RE
	  | From RE
	    deriving Eq


mkToNorm, mkFromNorm :: (AST e p) => RE -> (RE,e)
mkToNorm r = let n = norm r
		 e = eVar ("tn"++(reToFuncName r))
	     in (n, e)
mkFromNorm r = let n = norm r
		   e = eVar ("fn"++(reToFuncName r))
	       in (n, e)


---------------------------------------------------------------
--  wishComesTrue:                                           --
--     fulfills a wish by generating the code.               --
---------------------------------------------------------------
wishComesTrue :: (AST e p) =>  Wish -> e
wishComesTrue (To r) = let (_,e,_) = tnorm r
		       in e
wishComesTrue (From r) = let (_,_,e) = tnorm r
			 in e


wishList :: State -> [Wish]
wishList (State _ _ w) = w


---------------------------------------------------------------
-- reToFuncName :				             --
--    Takes a regular expression and return a legal haskell  --
-- function name                                             --
---------------------------------------------------------------
reToFuncName :: RE -> String
reToFuncName Em = "em"
reToFuncName (Lab l) = brackit ("lab"++l)
reToFuncName (Or r1 r2) = brackit ("or"++(reToFuncName r1)++(reToFuncName r2))
reToFuncName Ph = "ph"
reToFuncName (Pr r1 r2) = brackit ("pr"++(reToFuncName r1)++(reToFuncName r2))
reToFuncName (St r) = brackit ("st"++(reToFuncName r))

brackit :: String -> String
brackit s = "ob"++ s ++ "cb"


