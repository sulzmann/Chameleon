module X.REOpts 
    ( RE(..), isect, diff, lbreak, rbreak, lbreak_nd, rbreak_nd, norm, mono, mono', mono'', emptyword, sort_, lnf, insert_
--    , rr1, rr2
    )
where
-- module Main where

import Monad

data RE = Lab String
        | Or RE RE
        | Em
        | Ph
        | Pr RE RE
        | St RE
        | V Var
	| Var Int
          deriving (Eq, Ord)

-- not needed in new implementation.
data Var = Z
         | S Var
         | SL Var
         | SR Var
           deriving (Show,Eq, Ord)
----------------------------------- old implementation ----------------------------------


{-
type IGrammar = [(Var,(RE,RE))]
type OGrammar = [(Var,RE)]

--- RExRE -> Grammar
isect :: RE -> RE -> RE
isect r1 r2 = let g = istogr [] Z r1 r2 
                  r = grtore g Z
                  r3 = simplify r
              in r3

istogr :: IGrammar -> Var -> RE -> RE -> OGrammar
istogr g x r1 r2 = case (rhsin r1 r2 g) of
                   True  -> [(x,(V (glookup r1 r2 g)))]
                   False -> let g' = nistogr ((x,(r1,r2)):g) (S x) (norm r1) (norm r2)
                            in ((x,(V (S x))):g')

nistogr :: IGrammar -> Var -> RE -> RE -> OGrammar
nistogr g x Ph _ = [(x,Ph)]
nistogr g x _ Ph = [(x,Ph)]
nistogr g x (Or Em n1) (Or Em n2) = (x,(Or Em (V (S x)))):(nistogr g (S x) n1 n2)
nistogr g x (Or (Pr (Lab l1) r1) n1) (Or (Pr (Lab l2) r2) n2) | (l1 == l2) = let g' = istogr g (SL x) r1 r2
                                                                                 g'' = nistogr g (SR x) n1 n2
                                                                                 g''' = g' ++ g''
                                                                             in (x,(Or (Pr (Lab l1) (V (SL x))) (V (SR x)))):g'''
nistogr g x (Or m1 n1) (Or m2 n2) = case (m1 < m2) of
                                    True -> let g' = nistogr g (S x) n1 (Or m2 n2)
                                            in ((x,(V (S x))):g')
                                    False -> let g' = nistogr g (S x) (Or m1 n1) n2
                                             in ((x,(V (S x))):g')


diff :: RE -> RE -> RE
diff r1 r2 = let g = dftogr [] Z r1 r2
                 r = grtore g Z
                 r3 = simplify r
             in r3

dftogr :: IGrammar -> Var -> RE -> RE -> OGrammar
dftogr g x r1 r2 = case (rhsin r1 r2 g) of
                   True  -> [(x,(V (glookup r1 r2 g)))]
                   False -> let g' = ndftogr ((x,(r1,r2)):g) (S x) (norm r1) (norm r2)
                            in ((x,(V (S x))):g')

ndftogr :: IGrammar -> Var -> RE -> RE -> OGrammar
ndftogr g x Ph _ = [(x,Ph)]
ndftogr g x n Ph = [(x,n)]
ndftogr g x (Or Em n1) (Or Em n2) = (x,(V (S x))):(ndftogr g (S x) n1 n2)
ndftogr g x (Or (Pr (Lab l1) r1) n1) (Or (Pr (Lab l2) r2) n2) | (l1 == l2) = let g' = dftogr g (SL x) r1 r2
                                                                                 g'' = ndftogr g (SR x) n1 n2
                                                                                 g''' = g' ++ g''
                                                                             in (x,(Or (Pr (Lab l1) (V (SL x))) (V (SR x)))):g'''
ndftogr g x (Or m1 n1) (Or m2 n2) = case (m1 < m2) of
                                    True -> let g' = ndftogr g (S x) n1 (Or m2 n2)
                                            in ((x,(Or m1 (V (S x)))):g')
                                    False -> let g' = ndftogr g (S x) (Or m1 n1) n2
                                             in ((x,(V (S x))):g')


lquo :: RE -> RE -> RE
lquo r1 r2 = let g = lqtogr [] Z r1 r2
                 r = grtore g Z
                 r3 = simplify r
             in r3

lqtogr :: IGrammar -> Var -> RE -> RE -> OGrammar
lqtogr g x r1 r2 = case (rhsin r1 r2 g) of
                   True  -> [(x,(V (glookup r1 r2 g)))]
                   False -> let g' = nlqtogr ((x,(r1,r2)):g) (S x) (norm r1) (norm r2)
                            in ((x,(V (S x))):g')


nlqtogr :: IGrammar -> Var -> RE -> RE -> OGrammar
nlqtogr g x Ph _ = [(x,Ph)]
nlqtogr g x n Ph = [(x,Ph)]
nlqtogr g x Em n2 = [(x,n2)]
nlqtogr g x (Pr (Lab l1) r1) (Or (Pr (Lab l2) r2) n2) | (l1 == l2) = let g' = lqtogr g (S x) r1 r2
                                                                     in (x, (V (S x))) : g'

nlqtogr g x (Pr (Lab l1) r1) (Or m2 n2) | ((Pr (Lab l1) r1) < m2) = [(x,Ph)]
                                        | (m2 < (Pr (Lab l1) r1)) = let g' = nlqtogr g (S x) (Pr (Lab l1) r1) n2
                                                                       in (x,(V (S x))):g'

nlqtogr g x (Or m1 n1) n2 = let g' = nlqtogr g (SL x) m1 n2 
                                g'' = nlqtogr g (SR x) n1 n2
                            in (x,(Or (V (SL x)) (V (SR x)))):(g' ++ g'')

-- type Context = [((RE,RE),Int)]
rhsin :: RE -> RE -> IGrammar -> Bool
rhsin _ _ [] = False
rhsin r1 r2 ((_,rhs):g) = case ((r1,r2)==rhs) of
                          True -> True
                          False -> rhsin r1 r2 g

glookup :: RE -> RE -> IGrammar -> Var
glookup _ _ [] = undefined
glookup r1 r2 ((x,rhs):g) = case ((r1,r2)==rhs) of
                            True -> x
                            False -> glookup r1 r2 g

-- Grammar to RE
grtore :: OGrammar -> Var -> RE
grtore g x = let r' = glookuprhs x g
                 l  = rhsfv r'
                 l' = fvsgt l x
                 lr = mgrtore g l' 
                 r'' = applysubs r' l' lr
             in 
             case (rhshas x r'') of
             False -> r''
             True  -> rmrec x r''

glookuprhs :: Var -> OGrammar -> RE
glookuprhs x ((y,r):gs) = case (x == y) of
                          True -> r
                          False -> glookuprhs x gs

rhsfv :: RE -> [Var]
rhsfv Ph = []
rhsfv Em = []
rhsfv (V n) = [n]
rhsfv (Lab _) = []
rhsfv (Pr r1 r2) = (rhsfv r1) ++ (rhsfv r2)
rhsfv (Or r1 r2) = (rhsfv r1) ++ (rhsfv r2)
rhsfv (St r) = rhsfv r

fvsgt :: [Var] -> Var -> [Var]
fvsgt [] x = []
fvsgt (y:ys) x = case (gt y x) of
                 True -> y:(fvsgt ys x)
                 False -> fvsgt ys x

gt :: Var -> Var -> Bool
gt Z _ = False
gt (S n) Z = True
gt (S n) (S n') = gt n n'
gt (S n) (SL n') = gt n n'
gt (S n) (SR n') = gt n n'
gt (SL n) Z = True
gt (SL n) (S n') = gt n n'
gt (SL n) (SL n') = gt n n'
gt (SL n) (SR n') = gt n n'
gt (SR n) Z = True
gt (SR n) (S n') = gt n n'
gt (SR n) (SL n') = gt n n'
gt (SR n) (SR n') = gt n n'

mgrtore :: OGrammar -> [Var] -> [RE]
mgrtore g [] = []
mgrtore g (v:vs) = (grtore g v):(mgrtore g vs)

applysubs :: RE -> [Var] -> [RE] -> RE
applysubs r [] _ = r
applysubs r (v:vs) (e:es) = let r1 = applysub r v e
                            in (applysubs r1 vs es)

applysub :: RE -> Var -> RE -> RE
applysub Ph _ _ = Ph
applysub Em _ _ = Em
applysub (Lab l) _ _ = Lab l
applysub (Pr r1 r2) v e = Pr (applysub r1 v e) (applysub r2 v e)
applysub (Or r1 r2) v e = Or (applysub r1 v e) (applysub r2 v e)
applysub (St r) v e = St (applysub r v e)
applysub (V v) v' e = case (v == v') of
                      True -> e
                      False -> (V v)

rhshas :: Var -> RE -> Bool
rhshas _ Ph = False
rhshas _ Em = False
rhshas _ (Lab _) = False
rhshas x (Pr r1 r2) = (rhshas x r1)||(rhshas x r2)
rhshas x (Or r1 r2) = (rhshas x r1)||(rhshas x r2)
rhshas x (St r) = rhshas x r
rhshas x (V y) = (x == y)

rmrec :: Var -> RE -> RE
rmrec x r = let (l,m) =  rmrecsub x r
                b = isphi l
                b' = isphi m
            in rmrec' b b' x r l m

rmrecsub :: Var -> RE -> (RE,RE)
rmrecsub _ Ph = (Ph,Ph)
rmrecsub _ Em = (Ph,Em)
rmrecsub _ (Lab l) = (Ph,(Lab l))
rmrecsub x (Pr r r') = let (l,m) = rmrecsub x r' 
                       in ((Pr r l),(Pr r m))
rmrecsub x (Or r1 r2) = let (l1,m1) = rmrecsub x r1
                            (l2,m2) = rmrecsub x r2
                        in ((Or l1 l2),(Or m1 m2))
rmrecsub x (V v) = case (x == v) of
                   True -> (Em,Ph)
                   False -> (Ph, (V v))
rmrecsub x (St r) = (Ph,(St r))

rmrec' :: Bool -> Bool -> Var -> RE -> RE -> RE -> RE
rmrec' True True _ _ _ _ = Ph
rmrec' False True _ _ _ _ = Ph
rmrec' True False _ r _ _ = r
rmrec' False False _ r l m = (Pr (St l) m)

-}

----------------------------------- new implementation ----------------------------------

type Sys = [(Int,RE)]

-- Constructing Equation system
-- Contruction monad
data CState = CState { counter :: Int,
                       context :: [((RE,RE),Int)]
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

checkCS :: (RE,RE) -> CS (Maybe Int)
checkCS rs = CS (\st -> let ctxt = context st
		          in (st, (lookup rs ctxt)))

addCS :: ((RE,RE),Int) -> CS ()
addCS (rs,i) = CS (\st -> let cnt = counter st
			      ctxt = context st
                     in (CState { counter = cnt, context = ((rs,i):ctxt) }, ()))

getCS :: CS [((RE,RE),Int)]
getCS = CS (\st -> let ctxt = context st
		   in (st, ctxt))

delCS :: ((RE,RE),Int) -> CS ()
delCS (rs,i) = CS (\st -> let cnt = counter st
		              ctxt = context st
		     in (CState { counter = cnt, context = (filter (\e -> not (e== (rs,i))) ctxt) }, ()))

runCS :: CState -> CS a -> (CState,a)
runCS s (CS a) = a s


isect :: RE -> RE -> RE
isect r1 r2 = let s = newisect r1 r2
		  r = sys2re s 0
	      in simplify r



newisect :: RE -> RE -> Sys
newisect r1 r2 = case (runCS initCS (i2s 0 r1 r2)) of
		 (i,s) -> s
i2s :: Int -> RE -> RE -> CS Sys
i2s i r1 r2 | (r1 == r2) = return [(i,r1)]
--	    | otherwise  = ni2s i (norm r1) (norm r2)
            | otherwise = do {
			      res <- checkCS (r1,r2);
			      case res of
			      Just i' -> return [(i,(Var i'))]
			      Nothing -> do { i' <- newNum;
					      addCS ((r1,r2),i);
					      sys <- ni2s i' (norm r1) (norm r2);
                                              delCS ((r1,r2),i);
					      return ((i,(Var i')):sys)
					    }
			     }

ni2s :: Int -> RE -> RE -> CS Sys
ni2s i Ph _ = return [(i,Ph)]
ni2s i _ Ph = return [(i,Ph)]
ni2s i m1@(Pr (Lab l1) r1) m2@(Pr (Lab l2) r2) 
     | l1 == l2 = do { i' <- newNum;
		       sys <- i2s i' r1 r2;
		       return ((i,(Pr (Lab l1) (Var i'))):sys)
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

ni2s i (Or Em n1) (Or Em n2) = do {
				   i' <- newNum;
				   sys <- ni2s i' n1 n2;
				   return ((i,(Or Em (Var i'))):sys)
				  }
ni2s i (Or (m1@(Pr (Lab l1) r1)) n1) (Or (m2@(Pr (Lab l2) r2)) n2) 
    | (l1 == l2) = do { i1 <- newNum;
			sys1 <- ni2s i1 m1 m2;
			i2 <- newNum;
			sys2 <- ni2s i2 n1 n2;
			return ((i,(Or (Var i1) (Var i2))):(sys1++sys2))
		      }
ni2s i (Or m1 n1) (Or m2 n2) | m1 < m2 = ni2s i n1 (Or m2 n2)
			     | otherwise = ni2s i (Or m1 n1) n2



diff :: RE -> RE -> RE
diff r1 r2 = let s = newdiff r1 r2
		 r = sys2re s 0
	     in simplify r


newdiff :: RE -> RE -> Sys
newdiff r1 r2 = case (runCS initCS (d2s 0 r1 r2)) of
		 (i,s) -> s
d2s :: Int -> RE -> RE -> CS Sys
d2s i r1 r2 | (r1 == r2) = return [(i,Ph)]
--	    | otherwise  = nd2s i (norm r1) (norm r2)
	    | otherwise = do {
			      res <- checkCS (r1,r2);
			      case res of
			      Just i' -> return [(i,(Var i'))]
			      Nothing -> do { i' <- newNum;
					      addCS ((r1,r2),i);
					      sys <- nd2s i' (norm r1) (norm r2);
                                              delCS ((r1,r2),i);
					      return ((i,(Var i')):sys)
					    }
			     }

nd2s :: Int -> RE -> RE -> CS Sys
nd2s i Ph _ = return [(i,Ph)]
nd2s i n Ph = return [(i,n)]
nd2s i m1@(Pr (Lab l1) r1) m2@(Pr (Lab l2) r2) 
     | l1 == l2 = do { i' <- newNum;
		       sys <- d2s i' r1 r2;
		       return ((i,(Pr (Lab l1) (Var i'))):sys)
		     }
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
nd2s i (Or Em n1) (Or Em n2) = nd2s i n1 n2

nd2s i (Or (m1@(Pr (Lab l1) r1)) n1) (Or (m2@(Pr (Lab l2) r2)) n2) 
    | (l1 == l2) = do { i1 <- newNum;
			sys1 <- nd2s i1 m1 m2;
			i2 <- newNum;
			sys2 <- nd2s i2 n1 n2;
			return ((i,(Or (Var i1) (Var i2))):(sys1++sys2))
		      }
nd2s i (Or m1 n1) (Or m2 n2) | m1 < m2 = do {
					     i' <- newNum;
					     sys <- nd2s i' n1 (Or m2 n2);
					     return ((i,(Or m1 (Var i'))):sys)
					    }
			     | otherwise = nd2s i (Or m1 n1) n2





lquo :: RE -> RE -> RE
lquo r1 r2 = let s = newlquo r1 r2
		 r = sys2re s 0
             in simplify r

newlquo :: RE -> RE -> Sys
newlquo r1 r2 = case (runCS initCS (lq2s 0 r1 r2)) of
		(_,sys) -> sys


lq2s :: Int -> RE -> RE -> CS Sys
-- lq2s i r1 r2 = nlq2s i (norm r1) (norm r2)
lq2s i r1 r2 = do { res <- checkCS (r1,r2);
                    case res of 
                    Just i' -> return [(i,(Var i'))]
                    Nothing -> do { i' <- newNum;
                                    addCS ((r1,r2),i);
                                    sys <- nlq2s i' (norm r1) (norm r2);
                                    delCS ((r1,r2),i);
                                    return ((i,(Var i')):sys)
                                  }
                  }

nlq2s :: Int -> RE -> RE -> CS Sys
nlq2s i Ph _ = return [(i,Ph)]
nlq2s i _ Ph = return [(i,Ph)]
nlq2s i Em n = return [(i,n)]
nlq2s i m1@(Pr (Lab l1) r1) (Or (m2@(Pr (Lab l2) r2)) n2) 
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
    | (l1 == l2) = lq2s i r1 r2

nlq2s i (Pr (Lab l1) r1) (Or m2 n2) | ((Pr (Lab l1) r1) < m2) = return [(i,Ph)]
                                    | (m2 < (Pr (Lab l1) r1)) = nlq2s i (Pr (Lab l1) r1) n2
nlq2s i (Or m1 n1) n2 = do { i1 <- newNum;
			     i2 <- newNum;
			     sys1 <- nlq2s i1 m1 n2;
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



sys2re :: Sys -> Int -> RE
sys2re sys i = case (runSS initSS (sys2reM sys i)) of
	       (_,r) -> r

sys2reM :: Sys -> Int -> SS RE
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
    where freeVars :: RE -> [Int]       -- returns the set of free vars in a RE.
	  freeVars Ph = []
	  freeVars Em = []
	  freeVars (Var n) = [n]
	  freeVars (Lab _) = []
	  freeVars (Pr r1 r2) = (freeVars r1) ++ (freeVars r2)
	  freeVars (Or r1 r2) = (freeVars r1) ++ (freeVars r2)
	  freeVars (St r) = freeVars r
	  subs :: RE -> [(Int,RE)] -> RE -- applies subsitution Int-RE pairs to a RE.
	  subs Ph _ = Ph
	  subs Em _ = Em
	  subs (Var i) s = case (lookup i s) of
			   Just r -> r
			   Nothing -> (Var i)
	  subs (Lab l) _ = Lab l
	  subs (Pr r1 r2) s = Pr (subs r1 s) (subs r2 s)
	  subs (Or r1 r2) s = Or (subs r1 s) (subs r2 s)
	  subs (St r) s = St (subs r s)

-- apply Arden's law to remove recursion.
removeRec :: Int -> RE -> RE  --  remove the recursion of variable i.
{-
removeRec _ Ph = Ph
removeRec _ Em = Em
removeRec _ (Lab l) = (Lab l)
removeRec i (Pr r r') = Pr r (removeRec i r')
removeRec i (Or r r') = Or (removeRec i r) (removeRec i r')
removeRec i (Var i') = if (i == i') then Em else (Var i')
removeRec _ (St r) = St r
-}
removeRec i r = let (p1,p2) = prefixes i r   
	        in removeRec' (isphi p1) (isphi p2) r p1 p2
removeRec' :: Bool -> Bool -> RE -> RE -> RE -> RE
removeRec' _ True _ _ _ = Ph
removeRec' True False r _ _ = r
removeRec' False False _ p1 p2 = Pr (St p1) p2
prefixes :: Int -> RE -> (RE,RE) 
-- find the prefixes p1 and p2 such that ((p1,(var i)) | p2) = r
-- assumption : No variable occurs in non-tail position.
prefixes _ Ph = (Ph,Ph)
prefixes _ Em = (Ph,Em)
prefixes _ (Lab l) = (Ph,(Lab l))
prefixes i (Pr r r') = let (p1,p2) = prefixes i r'
		       in ((Pr r p1), (Pr r p2))
prefixes i (Or r r') = let (p1,p2) = prefixes i r
			   (p1',p2') = prefixes i r'
		       in ((Or p1 p1'),(Or p2 p2'))
prefixes i (Var i') = if (i == i') then (Em,Ph) else (Ph, (Var i'))
prefixes _ (St r) = (Ph,(St r))

------------------------------------- Common Codes ----------------------------------------------
rquo :: RE -> RE -> RE
rquo r1 r2 = let rr1 = reverse_ r1
                 rr2 = reverse_ r2
                 rr3 = lquo rr2 rr1
                 r3 = reverse_ rr3
             in r3


reverse_ :: RE -> RE
reverse_ Ph = Ph
reverse_ Em = Em
reverse_ (Lab l) = (Lab l)
reverse_ (Pr r1 r2) = Pr (reverse_ r2) (reverse_ r1)
reverse_ (Or r1 r2) = Or (reverse_ r1) (reverse_ r2)
reverse_ (St r) = St (reverse_ r)


ipi :: RE -> RE
ipi Ph = Ph
ipi Em = Or Em (Lab "$")
ipi (Lab l) = Pr (Or Em (Lab "$")) (Pr (Lab l) (Or Em (Lab "$")))
ipi (Pr r1 r2) = Pr (ipi r1) (Pr (Or (Lab "$") Em) (ipi r2))
ipi (Or r1 r2) = Or (ipi r1) (ipi r2)
ipi (St r) = St (Or r (Lab "$"))

break_ :: RE -> RE -> RE -> RE
break_ c l1 l2 = 
    let l1' = ipi l1
        a = diff l1' (Pr l1 (Lab "$"))
        c' = ipi c
        l' = diff (Pr l1 (Pr (Lab "$") l2)) (Pr a l2)
        o = isect c' l'
    in o



lbreak :: RE -> RE -> RE -> RE
lbreak c l1 l2 = let o' = break_ c l1 l2
                     o = rquo o' (Pr (Lab "$") l2)
                 in o

rbreak :: RE -> RE -> RE -> RE
rbreak c l1 l2 = let o' = break_ c l1 l2
                     o = lquo (Pr l1 (Lab "$")) o'
                 in o


lbreak_nd, rbreak_nd :: RE -> RE -> RE -> RE
lbreak_nd c l1 l2 = rquo c l2
rbreak_nd c l1 l2 = lquo l1 c





isphi :: RE -> Bool
isphi Ph = True
isphi Em = False
isphi (Lab _) = False
isphi (Pr r r') = (isphi r)||(isphi r')
isphi (Or r r') = (isphi r)&&(isphi r')
isphi (Var _) = False
isphi (St _) = False
isphi _ = False

simplify :: RE -> RE
simplify Ph = Ph
simplify Em = Em
simplify (Lab l) = (Lab l)
simplify (St r) = simplifystar (simplify r) (St r)
simplify (Pr r1 r2) = simplifypair (simplify r1) (simplify r2) 
simplify (Or r1 r2) = simplifyor (simplify r1) (simplify r2)

simplifystar :: RE -> RE -> RE
simplifystar Ph (St _) = Em
simplifystar Em (St _) = Em
simplifystar (St r) (St _) = St r
simplifystar r (St _) = St r

simplifypair :: RE -> RE -> RE
simplifypair Ph _ = Ph
simplifypair Em r = r
simplifypair (Lab l) Ph = Ph
simplifypair (Lab l) Em = Lab l
simplifypair (Lab l) r = Pr (Lab l) r
simplifypair (Pr r1 r2) Ph = Ph
simplifypair (Pr r1 r2) Em = Pr r1 r2
simplifypair (Pr r1 r2) r = Pr r1 (Pr r2 r)
simplifypair (St r) Ph = Ph
simplifypair (St r) Em = St r
simplifypair (St r) r' = Pr (St r) r'
simplifypair (Or r1 r2) Ph = Ph
simplifypair (Or r1 r2) Em = Or r1 r2
simplifypair (Or r1 r2) r = Pr (Or r1 r2) r
simplifypair r1 r2 = Pr (simplify r1) (simplify r2)

                           
simplifyor :: RE -> RE -> RE
simplifyor Ph r = r
simplifyor Em Ph = Em
simplifyor Em Em = Em
simplifyor Em (St r) = St r
simplifyor Em r = Or Em r
simplifyor (Lab l) Ph = Lab l
simplifyor (Lab l) r = Or (Lab l) r
simplifyor (Pr r1 r2) Ph = Pr r1 r2
simplifyor (Pr r1 r2) r = Or (Pr r1 r2) r
simplifyor (St r) Ph = St r
simplifyor (St r) Em = St r
simplifyor (St r) r' = Or (St r) r'
simplifyor (Or r1 r2) Ph = Or r1 r2
simplifyor (Or r1 r2) r = Or r1 (Or r2 r)
simplifyor r Ph = r
simplifyor r1 r2 = Or (simplify r1) (simplify r2)


norm :: RE -> RE
norm r =  lnf (sort_ (mono r))

mono :: RE -> [RE]
mono r = case (emptyword r) of
         True -> Em:(mono' r)
         False -> mono' r

emptyword :: RE -> Bool
emptyword Em = True
emptyword (St r) = True
emptyword (Pr r1 r2) = (emptyword r1)&&(emptyword r2)
emptyword (Or r1 r2) = (emptyword r1)||(emptyword r2)
emptyword r = False

mono' :: RE -> [RE]
mono' Ph = []
mono' Em = []
mono' (Lab l) = [(Pr (Lab l) Em)]
mono' (St r) = mono'' r (St r)
mono' (Or r1 r2) = (mono' r1)++(mono' r2)
mono' (Pr Ph _) = []
mono' (Pr Em r1) = mono' r1
mono' (Pr (Lab l) r1) = [(Pr (Lab l) r1)]
mono' (Pr (Pr r1 r2) r3) = mono' (Pr r1 (Pr r2 r3))
mono' (Pr (Or r1 r2) r3) = mono' (Or (Pr r1 r3) (Pr r2 r3))
mono' (Pr (St r1) r2) = (mono'' (St r1) r2)++(mono' r2)

mono'' :: RE -> RE -> [RE]
mono'' Em _ = []
-- mono'' Em r = mono' r
mono'' (Lab l) r = [(Pr (Lab l) r)]
mono'' (St r1) r2 = mono'' r1 (Pr (St r1) r2)
mono'' (Or r1 r2) r3 = (mono'' r1 r3)++(mono'' r2 r3)
mono'' (Pr Em r1) r2 = mono'' r1 r2
mono'' (Pr (Lab l) r1) r2 = [(Pr (Lab l) (Pr r1 r2))]
mono'' (Pr (Pr r1 r2) r3) r4 = mono'' (Pr r1 (Pr r2 r3)) r4
mono'' (Pr (Or r1 r2) r3) r4 = mono'' (Or (Pr r1 r3) (Pr r2 r3)) r4
mono'' (Pr (St r1) r2) r3 = (mono'' (St r1) (Pr r2 r3))++(mono'' r2 r3)


sort_ :: [RE] -> [RE]
sort_ [] = []
sort_ (m:ms) = insert_ m (sort_ ms)


insert_ :: RE -> [RE] -> [RE]
insert_ m [] = [m]
insert_ (Pr (Lab l) r) ((Pr (Lab l') r'):ms) =
    case (l == l') of
    True -> (Pr (Lab l) (smerge r r')):ms
    False -> -- case (leqt (Pr (Lab l) r) (Pr (Lab l') r')) of 
	     case ((Lab l) < (Lab l')) of 
             True -> (Pr (Lab l) r):((Pr (Lab l') r'):ms)
             False -> (Pr (Lab l') r'):(insert_ (Pr (Lab l) r) ms)
insert_ m (m':ms) = -- case (leqt m m') of 
		    case (m < m') of
		    True -> m:(m':ms)
		    False -> m':(insert_ m ms)    

smerge :: RE -> RE -> RE
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
                        
lnf :: [RE] -> RE
lnf [] = Ph
lnf (m:ms) = Or m (lnf ms)

instance Show RE where
    show Ph = "{}"
    show Em = "()"
    show (Lab l) = l
    show (Pr r1 r2) = "("++ (show r1) ++ "," ++ (show r2) ++ ")"
    show (Or r1 r2) = "("++ (show r1) ++ "|" ++ (show r2) ++ ")"
    show (St r) = "(" ++ (show r) ++ "*)"
    show (V n) = show n
    show (Var n) = show n



la = (Lab "A")
lb = (Lab "B")
lc = (Lab "C")

rr2 = Pr (St (Or la lb)) lc 

rr1 = Or (Pr (Or (Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc) (St lb)) lb) (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc)) lb) (Pr (Pr (Pr (Pr (Or (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb)) lb) (St la)) la) lc) 

r3 = Pr (Or (Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc) (St lb)) lb) (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc)) lb

r4 =Pr (Pr (Pr (Pr (Or (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb)) lb) (St la)) la) lc 

r5 = Pr (Pr (Pr (Or (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb)) lb) (St la)) la

r6 = Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la
r7 =  Or r6 (Pr r6 lb)
r8 = Pr (St (Or la lb)) la
r9 = Or r8 (Pr r8 lb)


t1 = St (Or lc (Or lb la))
t2 = St (Or lc lb)
t3 = St la

isty = Or (Pr (Or lb lc) (St (Or lb lc))) (Pr (St (Or lb lc)) (Pr la (St (Or lc (Or lb la)))))

main :: IO ()
main = putStrLn (show (sys2re (newisect r7 r7) 0))
