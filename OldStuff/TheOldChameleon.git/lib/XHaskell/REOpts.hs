module Main where


data RE = Lab String
        | Or RE RE
        | Em
        | Ph
        | Pr RE RE
        | St RE
        | V Var
          deriving (Eq)

data Var = Z
         | S Var
         | SL Var
         | SR Var
           deriving (Show,Eq)

type IGrammar = [(Var,(RE,RE))]
type OGrammar = [(Var,RE)]

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
nistogr g x (Or m1 n1) (Or m2 n2) = case (leqt m1 m2) of
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
ndftogr g x (Or m1 n1) (Or m2 n2) = case (leqt m1 m2) of
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

nlqtogr g x (Pr (Lab l1) r1) (Or m2 n2) | (leqt (Pr (Lab l1) r1) m2) = [(x,Ph)]
                                        | (leqt m2 (Pr (Lab l1) r1)) = let g' = nlqtogr g (S x) (Pr (Lab l1) r1) n2
                                                                       in (x,(V (S x))):g'

nlqtogr g x (Or m1 n1) n2 = let g' = nlqtogr g (SL x) m1 n2 
                                g'' = nlqtogr g (SR x) n1 n2
                            in (x,(Or (V (SL x)) (V (SR x)))):(g' ++ g'')


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
ipi Em = Or Em (Lab "Br")
ipi (Lab l) = Pr (Or Em (Lab "Br")) (Pr (Lab l) (Or Em (Lab "Br")))
ipi (Pr r1 r2) = Pr (ipi r1) (Pr (Or (Lab "Br") Em) (ipi r2))
ipi (Or r1 r2) = Or (ipi r1) (ipi r2)
ipi (St r) = St (Or r (Lab "Br"))

break_ :: RE -> RE -> RE -> RE
break_ c l1 l2 = 
    let l1' = ipi l1
        a = diff l1' (Pr l1 (Lab "Br"))
        c' = ipi c
        l' = diff (Pr l1 (Pr (Lab "Br") l2)) (Pr a l2)
        o = isect c' l'
    in o


lbreak :: RE -> RE -> RE -> RE
lbreak c l1 l2 = let o' = break_ c l1 l2
                     o = rquo o' (Pr (Lab "Br") l2)
                 in o

rbreak :: RE -> RE -> RE -> RE
rbreak c l1 l2 = let o' = break_ c l1 l2
                     o = lquo (Pr l1 (Lab "Br")) o'
                 in o


leqt :: RE -> RE -> Bool
leqt m1 m2 = let i1 = mtoint m1
                 i2 = mtoint m2
             in (i1 < i2)

mtoint :: RE -> Int
mtoint (Pr (Lab "A") _) = 0
mtoint (Pr (Lab "B") _) = 1
mtoint (Pr (Lab "Br") _) = 2
mtoint Em = 3

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

isphi :: RE -> Bool
isphi Ph = True
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
simplifypair (Or r1 r2) Em = Or r1 (Or r2 Em)
simplifypair (Or r1 r2) r = Or r1 (Or r2 r)
                           
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
    False -> case (leqt (Pr (Lab l) r) (Pr (Lab l') r')) of 
             True -> (Pr (Lab l) r):((Pr (Lab l') r'):ms)
             False -> (Pr (Lab l') r'):(insert_ (Pr (Lab l) r) ms)
insert_ m (m':ms) = case (leqt m m') of 
             True -> m:(m':ms)
             False -> m':(insert_ m ms)
    

smerge :: RE -> RE -> RE
smerge r1 r2 | (r1 == r2) = r1
             | otherwise = case r2 of 
                           (Or r1' r2') -> case (r1 == r1') of
                                           True -> r2
                                           False -> Or r1' (smerge r1 r2')
                           _ -> Or r1 r2
                        
lnf :: [RE] -> RE
lnf [] = Ph
lnf (m:ms) = Or m (lnf ms)

data Pat = VPat RE
         | PPat Pat Pat

infer :: RE -> [Pat] -> ([RE],[RE])
infer Ph [] = ([],[])
infer r (p:ps) = let pa = stript p
                     rp = isect r pa
                     r' = diff r rp
                     rg = infer1 rp p
                     (rps,rgs) = infer r' ps 
                 in ((rp:rps),(rg:rgs))

infer1 :: RE -> Pat -> RE
infer1 rp (PPat p1 p2) = let ra1 = stript p1
                             ra2 = stript p2
                             rp1 = lbreak rp ra1 ra2
                             rp2 = rbreak rp ra1 ra2
                             rg1 = infer1 rp1 p1
                             rg2 = infer1 rp2 p2
                         in (Pr rg1 rg2)
infer1 rp (VPat r) = isect rp r

stript :: Pat -> RE 
stript (VPat r) = r
stript (PPat p1 p2) = Pr (stript p1) (stript p2)



instance Show RE where
    show Ph = "{}"
    show Em = "()"
    show (Lab l) = l
    show (Pr r1 r2) = "("++ (show r1) ++ "," ++ (show r2) ++ ")"
    show (Or r1 r2) = "("++ (show r1) ++ "|" ++ (show r2) ++ ")"
    show (St r) = "(" ++ (show r) ++ "*)"
    show (V n) = show n

la = (Lab "A")
lb = (Lab "B")
lc = (Lab "Br")

ty = Pr (St la) (Or (Pr lb (Or (Pr la (St (Or la lb))) (Pr lb (St (Or la lb))) )) Em)

v = infer ty [(PPat (VPat (St la)) (VPat (St la))), (VPat (St (Or la lb)))]  

t1 = Pr (St (Or la lb)) lc
t2 = Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb )) lb) Em)) la) lc) (St lb)) lb
t3 = Pr (Pr (Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb) (St la)) la) lc
t3' = Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb) (St la)  --problematic!
t3'' = Pr (Pr (Pr (Pr (St (Or la lb)) la) (St lb)) lb) (St la)
t4 = Pr (St la) (Pr (Pr (St lb) lb) (Pr la (St (Or la lb))))
lquo' r1 r2 = let g = lqtogr [] Z r1 r2
              in g

rquo' r1 r2 = let rr1 = reverse_ r1
                  rr2 = reverse_ r2
              in rr1
--                  rr3 = lquo' rr2 rr1
--              in rr3

lbreak' c l1 l2 = let o' = break_ c l1 l2
                      o = rquo' o' (Pr (Lab "Br") l2)
                  in o

r1 = Pr (St la) (Pr (Pr lb (St lb)) (Pr la (St (Or la lb))))
r2 = St lb
r3 = St (Or la lb)

rr2 = Pr (St (Or la lb)) lc
rr1 = Or (Pr (Or (Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc) (St lb)) lb) (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc)) lb) (Pr (Pr (Pr (Pr (Or (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb)) lb) (St la)) la) lc)


rr11 = Pr (Or (Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc) (St lb)) lb) (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc)) lb
rr11' = Or (Pr (Pr (Pr (Pr (St (Or la lb)) la) lc) (St lb)) lb) (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc)
rr111' = Pr (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc) (St lb)) lb --bad
rr111'' =  Pr (Pr (Pr (Pr (St (Or la lb)) la) lc) (St lb)) lb -- good

rr112' =  Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc --bad
 
rr112'' = Pr (Pr (St (Or la lb)) la) lc -- good

rr12 = Pr (Pr (Pr (Pr (Or (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) (St lb)) lb)) lb) (St la)) la) lc

s1 = Pr (Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc) (St lb) --bad
s2 = Pr (Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) la) lc --bad

p1 = Pr (Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em)) lb --bad
p2 = Or (Pr (St (Or la lb)) la) (Or (Pr (St (Or la lb)) lb) Em) --bad


main :: IO ()
main = putStrLn (show (lquo' rr2 rr1))
       
