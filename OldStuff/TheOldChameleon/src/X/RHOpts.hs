module X.RHOpts 
    ( RH(..), isect, diff, lbreak, rbreak, norm, mono, mono', mono'', emptyword, sort_, lnf, insert_
    , normC, sortC, insertC, lnfC
    , rr1, rr2
    )
where
-- module Main where

import Monad
import List

data RH = Lab String RH
        | Or RH RH
        | Em
        | Ph
        | Pr RH RH
        | St RH
	| Var Int
        | Fix Int RH
          deriving (Eq, Ord)

----------------------------------- new implementation ----------------------------------

type Sys = [(Int,RH)]

-- Constructing Equation system
-- Contruction monad
data CState = CState { counter :: Int,
                       context :: [((RH,RH),Int)]
                     }

data CS a = CS (CState -> (CState,a))

instance Monad CS where
    -- return :: a -> CS a
    return a = CS (\l -> (l, a))

    -- (>>=) :: CS a -> (a -> CS b) -> CS b
    (CS f) >>= g = CS (\s -> let (s',a) = f $! s
		                 CS e = g $! a
                             in  e $! s')

initCS = CState { counter = 1, context = [] }

-- basic combinators (for lifting values into the monad)
(|>) :: Monad m => m (a -> b) -> m a -> m b
f |>  m = f >>= \g -> m >>= \r -> return (g $! r)

(||>) :: Monad m => (a -> b) -> m a -> m b
f ||> m = m >>= \r -> return (f $! r)


newNum :: CS Int
newNum = CS (\st -> let {cnt = counter st;
			 ctxt = context st;}
	            in (CState { counter = cnt + 1, context = ctxt }, cnt ))

checkCS :: (RH,RH) -> CS (Maybe Int)
checkCS rs = CS (\st -> let ctxt = context st
		          in (st, (lookup rs ctxt)))

addCS :: ((RH,RH),Int) -> CS ()
addCS (rs,i) = CS (\st -> let cnt = counter st
			      ctxt = context st
                     in (CState { counter = cnt, context = ((rs,i):ctxt) }, ()))

getCS :: CS [((RH,RH),Int)]
getCS = CS (\st -> let ctxt = context st
		   in (st, ctxt))

delCS :: ((RH,RH),Int) -> CS ()
delCS (rs,i) = CS (\st -> let cnt = counter st
		              ctxt = context st
		     in (CState { counter = cnt, context = (filter (\e -> not (e== (rs,i))) ctxt) }, ()))

runCS :: CState -> CS a -> (CState,a)
runCS s (CS a) = a s


isect :: RH -> RH -> RH
isect r1 r2 = let s = newisect r1 r2
		  r = sys2re s 0
	      in simplify r



newisect :: RH -> RH -> Sys
newisect r1 r2 = case (runCS initCS (i2s 0 r1 r2)) of
		 (i,s) -> s
i2s :: Int -> RH -> RH -> CS Sys
i2s i r1 r2 | (r1 == r2) = return [(i,r1)]
--	    | otherwise  = ni2s i (norm r1) (norm r2)
            | (isfix r1) = i2s i (unfold r1) r2
            | (isfix r2) = i2s i r1 (unfold r2)
            | otherwise = do {
			      res <- checkCS (r1,r2);
			      case res of
			      Just i' -> return [(i,(Var i'))]
			      Nothing -> do { i' <- newNum;
					      addCS ((r1,r2),i);
					      sys <- ni2s i' (norm r1) (normC r2);
                                              delCS ((r1,r2),i);
					      return ((i,(Var i')):sys)
					    }
			     }

ni2s :: Int -> RH -> RH -> CS Sys
ni2s i Ph _ = return [(i,Ph)]
ni2s i _ Ph = return [(i,Ph)]
ni2s i m1@(Pr (Lab l1 c1) r1) (Or (m2@(Pr (Lab l2 c2) r2)) ms2)
     | l1 == l2 = do { i1 <- newNum;
		       sys1 <- i2s i1 c1 c2;
                       i2 <- newNum;
                       sys2 <- i2s i2 r1 r2;
                       i3 <- newNum;
                       sys3 <- ni2s i3 m1 ms2;
		       return ((i,(Or (Pr (Lab l1 (Var i1)) (Var i2)) (Var i3))):(sys1++sys2++sys3))
		     }
{-
    | l1 == l2 = do { res <- checkCS (m1,m2);
		      case res of
		      Just i' -> return [(i,(Var i'))]
		      Nothing -> do {
				     i' <- newNum;
				     addCS ((m1,m2),i);
				     sys <- i2s i' r1 r2;
				     delCS ((m1,m2),i);
				     return ((i,(Pr (Lab l1) (Var i'))):sys)
				    }
		    }
-}

ni2s i (Or Em n1) (Or (Or Em Ph) n2) = do {
				           i' <- newNum;
				           sys <- ni2s i' n1 n2;
				           return ((i,(Or Em (Var i'))):sys)
				          }
ni2s i (Or (m1@(Pr (Lab l1 c1) r1)) n1) (Or (clu2@(Or (m2@(Pr (Lab l2 c2) r2)) _)) n2)
    | (l1 == l2) = do { i1 <- newNum;
			sys1 <- ni2s i1 m1 clu2;
			i2 <- newNum;
			sys2 <- ni2s i2 n1 (Or clu2 n2);
			return ((i,(Or (Var i1) (Var i2))):(sys1++sys2))
		      }
ni2s i (Or m1 n1) (Or (clu2@(Or m2 _)) n2) | m1 < m2 = ni2s i n1 (Or clu2 n2)
			                   | otherwise = ni2s i (Or m1 n1) n2




diff :: RH -> RH -> RH
diff r1 r2 = let s = newdiff r1 r2
		 r = sys2re s 0
	     in simplify r


newdiff :: RH -> RH -> Sys
newdiff r1 r2 = case (runCS initCS (d2s 0 r1 r2)) of
		 (i,s) -> s
d2s :: Int -> RH -> RH -> CS Sys
d2s i r1 r2 | (r1 == r2) = return [(i,Ph)]
--	    | otherwise  = nd2s i (norm r1) (norm r2)
            | (isfix r1) = d2s i (unfold r1) r2
            | (isfix r2) = d2s i r1 (unfold r2)
	    | otherwise = do {
			      res <- checkCS (r1,r2);
			      case res of
			      Just i' -> return [(i,(Var i'))]
			      Nothing -> let () = unsafePerformIO (putStrLn ((show r1) ++ "-" ++ (show r2)))
                                         in do { i' <- newNum;
					         addCS ((r1,r2),i);
					         sys <- nd2s i' (norm r1) (normC r2);
                                                 delCS ((r1,r2),i);
					         return ((i,(Var i')):sys)
					       }
			     }

nd2s :: Int -> RH -> RH -> CS Sys
nd2s i Ph _ = return [(i,Ph)]
nd2s i n Ph = return [(i,n)]
nd2s i m1@(Pr (Lab l1 c1) r1) (Or (m2@(Pr (Lab l2 c2) r2)) ms2)
     | l1 == l2 = let (cs,rs) = extract (Or m2 ms2) 
                      ccs = map aux2 (combination cs)
                      crs = map aux2 (combination rs)
                  in do { (r,sys) <- aux1 (ccs,(reverse crs));
                          return ((i,r):sys)
		        }
     where aux1 :: ([RH],[RH]) -> CS (RH,Sys)
           aux1 ([],[]) = return (Ph,[])
           aux1 ((c:cs),(r:rs)) = do { i1 <- newNum;
                                       sys1 <- d2s i1 c1 c;
                                       i2 <- newNum;
                                       sys2 <- d2s i2 r1 r;
                                       (r,s) <- aux1 (cs,rs);
                                       return ((Or (Pr (Lab l1 (Var i1)) (Var i2)) r),((sys1++sys2)++s))
                                     }
           aux2 :: [RH] -> RH
           aux2 [] = Ph
           aux2 (m:ms) = Or m (aux2 ms)
{-
           aux3 :: [RH] -> [RH]
           aux3 [] = []
           aux3 (r:rs) = aux4 r (aux3 rs)
           aux4 :: RH -> [RH] -> [RH]
           aux4 r [] = [r]
           aux4 r (r':rs) | r == r' = (r':rs)
                          | r < r' = r:(r':rs)
                          | r > r' = r':(aux4 r rs)
-}

{-
    | l1 == l2 = do { res <- checkCS (m1,m2);
		      case res of
		      Just i' -> return [(i,(Var i'))]
		      Nothing -> do {
				     i' <- newNum;
				     addCS ((m1,m2),i);
				     sys <- d2s i' r1 r2;
				     delCS ((m1,m2),i);
				     return ((i,(Pr (Lab l1) (Var i'))):sys)
				    }
		    }
-}
nd2s i (Or Em n1) (Or (Or Em Ph) n2) = nd2s i n1 n2

nd2s i (Or (m1@(Pr (Lab l1 c1) r1)) n1) (Or (clu2@(Or (m2@(Pr (Lab l2 c2) r2)) _)) n2)
    | (l1 == l2) = do { i1 <- newNum;
			sys1 <- nd2s i1 m1 clu2;
			i2 <- newNum;
			sys2 <- nd2s i2 n1 (Or clu2 n2);
			return ((i,(Or (Var i1) (Var i2))):(sys1++sys2))
		      }
nd2s i (Or m1 n1) (Or (clu2@(Or m2 _)) n2) | m1 < m2 = do { i' <- newNum;
							    sys <- nd2s i' n1 (Or clu2 n2);
							    return ((i,(Or m1 (Var i'))):sys)
							  }
					   | otherwise = nd2s i (Or m1 n1) n2


extract :: RH -> ([RH],[RH])
extract Ph = ([],[])
extract (Or (Pr (Lab _ c) r) ms) = let (cs,rs) = extract ms
				   in  ((c:cs), (r:rs))


combination :: [a] -> [[a]]
combination [] = [[]]
combination (x:xs) = let c = combination xs 
                     in (map (x:) c) ++ c




lquo :: RH -> RH -> RH
lquo r1 r2 = let s = newlquo r1 r2
		 r = sys2re s 0
             in simplify r

newlquo :: RH -> RH -> Sys
newlquo r1 r2 = case (runCS initCS (lq2s 0 r1 r2)) of
		(_,sys) -> sys


lq2s :: Int -> RH -> RH -> CS Sys
-- lq2s i r1 r2 = nlq2s i (norm r1) (norm r2)
lq2s i r1 r2 | (isfix r1) = lq2s i (unfold r1) r2
	     | (isfix r2) = lq2s i r1 (unfold r2)
	     | otherwise = do { res <- checkCS (r1,r2);
				case res of 
				Just i' -> return [(i,(Var i'))]
				Nothing -> do { i' <- newNum;
						addCS ((r1,r2),i);
						sys <- nlq2s i' (norm r1) (normC r2);
						delCS ((r1,r2),i);
						return ((i,(Var i')):sys)
					      }
			      }

nlq2s :: Int -> RH -> RH -> CS Sys
nlq2s i Ph _ = return [(i,Ph)]
nlq2s i _ Ph = return [(i,Ph)]
nlq2s i Em n = return [(i,n)]
nlq2s i m1@(Pr (Lab l1 c1) r1) (Or (m2@(Pr (Lab l2 c2) r2)) ms2) 
{-
    | (l1 == l2) = do { res <- checkCS (m1,m2);
			case res of 
			Just i' -> return [(i,(Var i'))]
			Nothing -> do { i' <- newNum;
				        addCS ((m1,m2),i);
				        sys <- lq2s i' r1 r2;
				        delCS ((m1,m2),i);
				        return ((i,(Var i')):sys)
				      }
		      }
-}
    | (l1 == l2) = if (isphi [] (isect c1 c2)) 
		   then nlq2s i m1 ms2
		   else do { i1 <- newNum;
			     sys1 <- lq2s i1 r1 r2;
			     i2 <- newNum;
			     sys2 <- nlq2s i2 m1 ms2;
			     return ((i,(Or (Var i1) (Var i2))):(sys1++sys2))
			   }

nlq2s i (m1@(Pr (Lab l1 c1) r1)) (Or (clu2@(Or (m2@(Pr (Lab l2 c2) r2)) _)) _)
    | (l1 == l2) = nlq2s i m1 clu2

nlq2s i (Pr (Lab l1 c1) r1) (Or (clu2@(Or m2 _)) n2) | ((Pr (Lab l1 c1) r1) < m2) = return [(i,Ph)]
						     | (m2 < (Pr (Lab l1 c1) r1)) = nlq2s i (Pr (Lab l1 c1) r1) n2
nlq2s i (Or m1 n1) n2 = do { i1 <- newNum;
			     sys1 <- nlq2s i1 m1 n2;
			     i2 <- newNum;
			     sys2 <- nlq2s i2 n1 n2;
			     return ((i,(Or (Var i1) (Var i2))):(sys1++sys2))
			   }

-- Solving Equation System
-- Solver monad

data SState = SState { history :: [Int] }

data SS a = SS (SState -> (SState,a))

instance Monad SS where
    -- return :: a -> SS a
    return a = SS (\l -> (l, a))

    -- (>>=) :: SS a -> (a -> SS b) -> SS b
    (SS f) >>= g = SS (\s -> let (s',a) = f $! s
		                 SS e = g $! a
                             in  e $! s')

initSS = SState { history = [] }

getSS :: SS [Int]
getSS = SS (\st -> let h = history st
	           in (st, h))

addSS :: Int -> SS ()
addSS i = SS (\st -> let h = history st
                     in (SState { history = (i:h) }, ()))

delSS :: Int -> SS ()
delSS i = SS (\st -> let h = history st
		     in (SState { history = (filter (\e -> not (e == i)) h) }, ()))

runSS :: SState -> SS a -> (SState,a)
runSS s (SS a) = a s



sys2re :: Sys -> Int -> RH
sys2re sys i = case (runSS initSS (sys2reM sys i)) of
	       (_,r) -> r

sys2reM :: Sys -> Int -> SS RH
sys2reM sys i = case (lookup i sys) of
		Nothing -> error "sys2re error."
		Just r -> let is = freeVars r
		          in do {
				 addSS i;
				 h <- getSS;
				 let is' = filter (\i' -> not (elem i' h)) is
				 in do { 
					rs <- mapM (sys2reM sys) is';
--					delSS i;
					let s = zip is' rs
					    r' = subs r s
					in 
					if (elem i (freeVars r'))
					then return (removeRec i r')
					else return r'
				       }
				}

freeVars :: RH -> [Int]       -- returns the set of free vars in a RH.
freeVars Ph = []
freeVars Em = []
freeVars (Var n) = [n]
freeVars (Lab _ c) = freeVars c
freeVars (Pr r1 r2) = (freeVars r1) ++ (freeVars r2)
freeVars (Or r1 r2) = (freeVars r1) ++ (freeVars r2)
freeVars (St r) = freeVars r
freeVars (Fix i r) = filter (\j -> not (i == j)) (freeVars r)


subs :: RH -> [(Int,RH)] -> RH -- applies subsitution Int-RH pairs to a RH.
subs Ph _ = Ph
subs Em _ = Em
subs (Var i) s = case (lookup i s) of
		 Just r -> r
		 Nothing -> (Var i)
subs (Lab l r) s = Lab l (subs r s)
subs (Pr r1 r2) s = Pr (subs r1 s) (subs r2 s)
subs (Or r1 r2) s = Or (subs r1 s) (subs r2 s)
subs (St r) s = St (subs r s)
subs (Fix i r) s = Fix i (subs r s)


-- apply Arden's law to remove recursion.
removeRec :: Int -> RH -> RH  --  remove the recursion of variable i.
removeRec i r = Fix i r

{-
removeRec i r = let (p1,p2) = prefixes i r   
	        in removeRec' (isphi p1) (isphi p2) r p1 p2
removeRec' :: Bool -> Bool -> RH -> RH -> RH -> RH
removeRec' _ True _ _ _ = Ph
removeRec' True False r _ _ = r
removeRec' False False _ p1 p2 = Pr (St p1) p2
-}


------------------------------------- Common Codes ----------------------------------------------
rquo :: RH -> RH -> RH
rquo r1 r2 = let rr1 = reverse_ r1
                 rr2 = reverse_ r2
                 rr3 = lquo rr2 rr1
                 r3 = reverse_ rr3
             in r3


reverse_ :: RH -> RH
reverse_ Ph = Ph
reverse_ Em = Em
reverse_ (Lab l c) = Lab l c
reverse_ (Var i) = Var i
reverse_ (Pr r1 r2) = Pr (reverse_ r2) (reverse_ r1)
reverse_ (Or r1 r2) = Or (reverse_ r1) (reverse_ r2)
reverse_ (St r) = St (reverse_ r)
reverse_ (Fix i r) = Fix i (reverse_ r) -- fixme: is it complete?


ipi :: RH -> RH
ipi Ph = Ph
ipi Em = Or Em (Lab "$" Em) 
ipi (Lab l c) = Pr (Or Em (Lab "$" Em)) (Pr (Lab l c) (Or Em (Lab "$" Em)))
ipi (Pr r1 r2) = Pr (ipi r1) (Pr (Or (Lab "$" Em) Em) (ipi r2))
ipi (Or r1 r2) = Or (ipi r1) (ipi r2)
ipi (St r) = St (Or r (Lab "$" Em))
ipi (Var i) = (Var i) -- fixme: is it correct?
ipi (Fix i r) = Fix i (ipi r)

break_ :: RH -> RH -> RH -> RH
break_ c l1 l2 = 
    let l1' = ipi l1
        a = diff l1' (Pr l1 (Lab "$" Em))
        c' = ipi c
        l' = diff (Pr l1 (Pr (Lab "$" Em) l2)) (Pr a l2)
        o = isect c' l'
    in o


lbreak :: RH -> RH -> RH -> RH
lbreak c l1 l2 = let o' = break_ c l1 l2
                     o = rquo o' (Pr (Lab "$" Em) l2)
                 in o

rbreak :: RH -> RH -> RH -> RH
rbreak c l1 l2 = let o' = break_ c l1 l2
                     o = lquo (Pr l1 (Lab "$" Em)) o'
                 in o

cut :: RH -> String -> RH
cut r l = ncut (norm r) l

ncut :: RH -> String -> RH
ncut Ph _ = Ph
ncut (Or (Pr (Lab l c) r) n) l' | (l==l') && (emptyword r) = Or c (ncut n l)
				| otherwise = ncut n l
ncut (Or _ n) l = ncut n l


isphi :: [Int] -> RH -> Bool
isphi _ Ph = True
isphi _ Em = False
isphi c (Lab _ r) = isphi c r
isphi c (Pr r r') = (isphi c r)||(isphi c r')
isphi c (Or r r') = (isphi c r)&&(isphi c r')
isphi c (Var i) = elem i c
isphi _ (St _) = False
isphi c (Fix i r) = isphi (i:c) r

simplify :: RH -> RH
simplify Ph = Ph
simplify Em = Em
simplify (St r) = simplifystar (simplify r) (St r)
simplify (Var i) = Var i
simplify r = if (isphi [] r) then Ph
	     else  
	     case r of
	     (Lab l r) -> Lab l (simplify r)
	     (Pr r1 r2) -> simplifypair (simplify r1) (simplify r2) 
	     (Or r1 r2) -> simplifyor (simplify r1) (simplify r2)
	     (Fix i r) -> simplifyfix (Fix i r)

simplifystar :: RH -> RH -> RH
simplifystar Ph (St _) = Em
simplifystar Em (St _) = Em
simplifystar (St r) (St _) = St r
simplifystar r (St _) = St r

simplifypair :: RH -> RH -> RH
simplifypair Ph _ = Ph
simplifypair Em r = r
simplifypair (Lab _ _) Ph = Ph
simplifypair (Lab l r) Em = Lab l r
simplifypair (Lab l r') r = Pr (Lab l r') r
simplifypair (Pr r1 r2) Ph = Ph
simplifypair (Pr r1 r2) Em = Pr r1 r2
simplifypair (Pr r1 r2) r = Pr r1 (Pr r2 r)
simplifypair (St r) Ph = Ph
simplifypair (St r) Em = St r
simplifypair (St r) r' = Pr (St r) r'
simplifypair (Or r1 r2) Ph = Ph
simplifypair (Or r1 r2) Em = Or r1 (Or r2 Em)
simplifypair (Or r1 r2) r = Or r1 (Or r2 r)
simplifypair r1 r2 = Pr (simplify r1) (simplify r2)
                           
simplifyor :: RH -> RH -> RH
simplifyor Ph r = r
simplifyor Em Ph = Em
simplifyor Em Em = Em
simplifyor Em (St r) = St r
simplifyor Em r = Or Em r
simplifyor (Lab l r) Ph = Lab l r
simplifyor (Lab l r') r = Or (Lab l r') r
simplifyor (Pr r1 r2) Ph = Pr r1 r2
simplifyor (Pr r1 r2) r = Or (Pr r1 r2) r
simplifyor (St r) Ph = St r
simplifyor (St r) Em = St r
simplifyor (St r) r' = Or (St r) r'
simplifyor (Or r1 r2) Ph = Or r1 r2
simplifyor (Or r1 r2) r = Or r1 (Or r2 r)
simplifyor r Ph = r
simplifyor r1 r2 = Or (simplify r1) (simplify r2)

simplifyfix :: RH -> RH
simplifyfix (Fix i r) = let r'= (simplify r)
			in if tailrec i r'
			   then let (p1,p2) = prefixes i r'   -- can be turned into kleene-star
				in case ((isphi [] p1),(isphi [] p2)) of
				   (_,True) -> Ph
				   (True,False) -> p2
				   (False,False) -> simplify (Pr (St p1) p2)
		           else Fix i r'
				
tailrec :: Int -> RH -> Bool
tailrec i Ph = True
tailrec i Em = True
tailrec i (Pr r1 r2) = (not (elem i (freeVars r1)))&&(tailrec i r2)
tailrec i (Or r1 r2) = (tailrec i r1)&&(tailrec i r2)
tailrec i (Var j) | i == j = True
tailrec i r = not (elem i (freeVars r))


prefixes :: Int -> RH -> (RH,RH) 
-- find the prefixes p1 and p2 such that ((p1,(var i)) | p2) = r
-- assumption : No variable occurs in non-tail position.
prefixes _ Ph = (Ph,Ph)
prefixes _ Em = (Ph,Em)
prefixes _ (Lab l r) = (Ph,(Lab l r))
prefixes i (Pr r r') = let (p1,p2) = prefixes i r'
		       in ((Pr r p1), (Pr r p2))
prefixes i (Or r r') = let (p1,p2) = prefixes i r
			   (p1',p2') = prefixes i r'
		       in ((Or p1 p1'),(Or p2 p2'))
prefixes i (Var i') = if (i == i') then (Em,Ph) else (Ph, (Var i'))
prefixes _ (St r) = (Ph,(St r))



norm :: RH -> RH
norm r =  lnf (sort_ (mono r))

mono :: RH -> [RH]
mono r = case (emptyword r) of
         True -> Em:(mono' r)
         False -> mono' r

emptyword :: RH -> Bool
emptyword Em = True
emptyword (St r) = True
emptyword (Pr r1 r2) = (emptyword r1)&&(emptyword r2)
emptyword (Or r1 r2) = (emptyword r1)||(emptyword r2)
emptyword (Fix i r) = emptyword (unfold (Fix i r))
emptyword r = False

mono' :: RH -> [RH]
mono' Ph = []
mono' Em = []
mono' (Lab l r) = [(Pr (Lab l r) Em)]
mono' (St r) = mono'' r (St r)
mono' (Or r1 r2) = (mono' r1)++(mono' r2)
mono' (Pr Ph _) = []
mono' (Pr Em r1) = mono' r1
mono' (Pr (Lab l r1') r1) = [(Pr (Lab l r1') r1)]
mono' (Pr (Pr r1 r2) r3) = mono' (Pr r1 (Pr r2 r3))
mono' (Pr (Or r1 r2) r3) = mono' (Or (Pr r1 r3) (Pr r2 r3))
mono' (Pr (St r1) r2) = (mono'' (St r1) r2)++(mono' r2)
mono' (Pr (Fix i r1) r2) = mono' (Pr (unfold (Fix i r1)) r2)
mono' (Fix i r) = mono' (unfold (Fix i r))

mono'' :: RH -> RH -> [RH]
mono'' Em _ = []
-- mono'' Em r = mono' r
mono'' (Lab l r') r = [(Pr (Lab l r') r)]
mono'' (St r1) r2 = mono'' r1 (Pr (St r1) r2)
mono'' (Fix i r1) r2 = mono'' (unfold (Fix i r1)) r2
mono'' (Or r1 r2) r3 = (mono'' r1 r3)++(mono'' r2 r3)
mono'' (Pr Em r1) r2 = mono'' r1 r2
mono'' (Pr (Lab l r1') r1) r2 = [(Pr (Lab l r1') (Pr r1 r2))]
mono'' (Pr (Pr r1 r2) r3) r4 = mono'' (Pr r1 (Pr r2 r3)) r4
mono'' (Pr (Or r1 r2) r3) r4 = mono'' (Or (Pr r1 r3) (Pr r2 r3)) r4
mono'' (Pr (St r1) r2) r3 = (mono'' (St r1) (Pr r2 r3))++(mono'' r2 r3)
mono'' (Pr (Fix i r1) r2) r3 = mono'' (Pr (unfold (Fix i r1)) r2) r3

sort_ :: [RH] -> [RH]
sort_ [] = []
sort_ (m:ms) = insert_ m (sort_ ms)


insert_ :: RH -> [RH] -> [RH]
insert_ m [] = [m]
insert_ (m@(Pr (Lab l c) r)) ((m'@(Pr (Lab l' c') r')):ms) =
    case (l == l') of
    True -> m:(m':ms)
    False -> case ((Lab l c) < (Lab l' c')) of 
             True -> m:(m':ms)
             False -> m':(insert_ m ms)
insert_ m (m':ms) = case (m < m') of
		    True -> m:(m':ms)
		    False -> m':(insert_ m ms)    
                        
lnf :: [RH] -> RH
lnf [] = Ph
lnf (m:ms) = Or m (lnf ms)


-- special norm function that builds a union of CLUs instead of monomials
normC :: RH -> RH
normC r = lnfC (sortC (mono r))


sortC :: [RH] -> [[RH]]
sortC [] = []
sortC (m:ms) = insertC m (sortC ms)


insertC :: RH -> [[RH]] -> [[RH]]
insertC m [] = [[m]]
insertC (m@(Pr (Lab l c) r)) (((m'@(Pr (Lab l' c') r')):ms):clus) =
    case (l == l') of
    True -> --(m:(m':ms)):clus
            (smergeC m (m':ms)):clus
    False -> case ((Lab l c) < (Lab l' c')) of 
             True -> [m]:((m':ms):clus)
             False -> (m':ms):(insertC m clus)
insertC m ((clu@(m':ms)):clus) = case (m < m') of
		                 True -> [m]:(clu:clus)
		                 False -> clu:(insertC m clus)    

-- simplify the CLUs
smergeC :: RH -> [RH] -> [RH]
smergeC r [] = [r]
smergeC (Pr (Lab l c1) r1) ((Pr (Lab _ c2) r2):rs) 
        | c1 == c2 = (Pr (Lab l c1) (smerge r1 r2)):rs
	| c1 < c2  = (Pr (Lab l c1) r1):((Pr (Lab l c2) r2):rs)
	| c1 > c2  = (Pr (Lab l c2) r2):(smergeC (Pr (Lab l c1) r1) rs)
{-
smergeC r (r':rs) | r == r' = (r':rs)
                  | r < r' = r:(r':rs)
                  | r > r' = r':(smergeC r rs)
-}


smerge :: RH -> RH -> RH
smerge r1 r2 | (r1 == r2) = r1
             | otherwise = case r2 of 
                           (Or r1' r2') -> case (r1 == r1') of
                                           True -> r2
                                           False -> case (r1 > r1') of
                                                    True -> Or r1' (smerge r1 r2')
                                                    False -> Or r1 (Or r1' r2')
                           _ -> case (r1 > r2) of
                                True -> Or r2 r1
                                False -> Or r1 r2


                        
lnfC :: [[RH]] -> RH
lnfC [] = Ph
lnfC (clu:clus) = Or (lnfC' clu) (lnfC clus)

lnfC' :: [RH] -> RH
lnfC' [] = Ph
lnfC' (m:ms) = Or m (lnfC' ms)



unfold :: RH -> RH
unfold (Fix i r) = subs r [(i,(Fix i r))]

isfix :: RH -> Bool
isfix (Fix _ _) = True
isfix _ = False


instance Show RH where
    show Ph = "{}"
    show Em = "()"
    show (Lab l r) = l++"["++(show r)++"]"
    show (Pr r1 r2) = "("++ (show r1) ++ "," ++ (show r2) ++ ")"
    show (Or r1 r2) = "("++ (show r1) ++ "|" ++ (show r2) ++ ")"
    show (St r) = "(" ++ (show r) ++ "*)"
    show (Var n) = show n
    show (Fix i r) = "\\"++(show i)++"." ++ (show r)


la = Lab "A" Em

lb = Lab "B" Em

lc = Lab "C" Em

ld = Lab "D" Em

fixa = Fix (-1) (Or Em (Pr (Lab "A" Em) (Var (-1))))

t = Fix (-1) (Or Em (Lab "A" (Var (-1))))

t' = Fix (-1) (Or Em (Lab "A" (Lab "A" (Var (-1)))))

nt = Fix (-1) (Lab "A" (Var (-1)))


r5 = Pr (Or (Pr (St la) la) Em) la
r6 = Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la
r7 =  Or r6 (Pr r6 lb)

la1 = Lab "A" lb
la2 = Lab "A" lc
la3 = Lab "A" ld



{-
main :: IO ()
main = putStrLn (show (sys2re (newisect r7 r7) 0))
-}