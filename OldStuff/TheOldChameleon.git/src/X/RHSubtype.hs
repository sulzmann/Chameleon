------------------------------------------------------
-- The regular hedge subtyping proof system    --
------------------------------------------------------
module Core.RHSubtype 
    ( runST, initState, ucast, dcast, nucast, ndcast, norm, tmono
    ) where

import Core.ISubtype
import Core.IAST
import Core.RHOpts hiding (norm,normC)
import Misc.ErrorMsg
import Misc

data State = State { counter :: Int,
                     context :: [((RH,RH),String)]
                   }

data ST a = ST (State -> (State,a))

runST :: State -> ST a -> (State,a)
runST s (ST a) = a s

initState = State { counter = 1, context = [] }

instance Monad ST where
    -- return :: a -> ST a
    return a = ST (\l -> (l, a))

    -- (>>=) :: ST a -> (a -> ST b) -> ST b
    (ST f) >>= g = ST (\s -> let (s',a) = f $! s
				 ST e = g $! a
                             in  e $! s')

instance Env ST (RH,RH) where
--  newName :: ST String
    newName = ST (\st -> let cnt = counter st
                             ctxt = context st
                         in (State { counter = cnt + 1, context = ctxt }, "f"++(show cnt) ))
--  check :: (RH,RH) -> ST (Maybe String)
    check rs = ST (\st -> let ctxt = context st
                          in (st, (lookup rs ctxt)))
--  add :: ((RH,RH),String) -> ST ()
    add (rs,name) = ST (\st -> let cnt = counter st
                                   ctxt = context st
                               in (State { counter = cnt, context = ((rs,name):ctxt) }, ()))
--  del :: ((RH,RH),String) -> ST ()
    del (rs,name) = ST (\st -> let cnt = counter st
                                   ctxt = context st
                               in (State { counter = cnt, context = (filter (rs,name) ctxt) }, ()))
                    where filter _ [] = []
                          filter e (e':es) | e == e'   = es
                                           | otherwise = e':(filter e es)

instance UCast RH RH where
    ucast r1 r2 | (r1 == r2) = return (eAbs (pVar "u") (eVar "u")) -- build an identity function
		| otherwise  = -- return (eVar ((show r1)++(show r2)))
                               let (n1,tn1,_) = norm r1
                                   (n2,_,fn2) = normC r2
                               in 
                                  do { 
				       nu <- nucast n1 n2;
                                       return (eAbs (pVar "u") (fn2 `eApp` (nu `eApp` (tn1 `eApp` (eVar "u")))))
                                     }

instance NUCast RH RH where
    nucast Ph n = return (eError ("u"++(show Ph)++"->"++(show n))) -- eUndefined       -- phi <: r is always true, but the proof term is not needed. 
    nucast (Or Em n1') (Or (Or Em Ph) n2') = 
	do {
	    nu <- nucast n1' n2';
	    return (eAbs (pVar "nu")  
		    (eCase (eVar "nu")
		     [ ((pL pNil), (eL (eL eNil)))
		     , ((pR (pVar "z")), (eR (nu `eApp` (eVar "z"))))
		     ]));
           }
    nucast (Or (m1@(Pr (Lab l1 c1) r1)) n1') (Or (m2@(Pr (Lab l2 c2) r2)) n2') | l1 == l2 =
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
    nucast n1 n2 = bug ("Proof failed at UCast:" ++ (show n1) ++ " is not a subtype of " ++ (show n2)) -- fixme: error mesg

instance DCast RH RH where
    dcast r1 r2 | (r1 == r2) = return (eAbs (pVar "d") (eJust (eVar "d")))
                | otherwise  = let (n1,_,fn1) = norm r1
                                   (n2,tn2,_) = norm r2
                               in do {
                                      nd <- ndcast n1 n2;
                                      return (eAbs (pVar "d") 
				              (eCase (nd `eApp` (tn2 `eApp` (eVar "d")))
				               [ ((pJust (pVar "n1")), (eJust (fn1 `eApp` (eVar "n1"))))
				               , (pNothing, eNothing)]))
                                     }


instance NDCast RH RH where
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
    ndcast n1 n2 = bug ("Proof failed at DCast:" ++ (show n1) ++ " is not a subtype of " ++ (show n2)) -- fixme: error mesg

