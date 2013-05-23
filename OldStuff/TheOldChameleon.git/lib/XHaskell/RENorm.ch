module XHaskell.RENorm where

import XHaskell.RETypes

--------------------------Normalization -----------------------
-- 29.06 : I added cases to handle PHI, due to the implementation
-- of Lbreak and Rbreak
class Norm r n | r -> n 
{-  where
    norm :: r -> n
-}

instance ( Mono r l
         , Sort l l'
         , Lnf l' n
-- only needed in GHC 6.2
         , MonoSub b r l, Emptyword r b
         ) => Norm r n 
{-    
    where
    norm x = lnf (sort (mono x))
-}

class Mono r l | r -> l 
{-
    where
    mono :: r -> l
-}

instance ( Emptyword r b
         , MonoSub b r l
         ) => Mono r l 
{-
    where
    mono r = monosub (emptyword r) r
-}

class MonoSub b r l | b r -> l 
{-
    where
    monosub :: b -> r -> l
-}
instance ( Mono' r l
         ) => MonoSub T r (XHaskell.RETypes.C EMPT l) 
{-
    where
    monosub _ r = C EMPT (mono' r)
-}
instance ( Mono' r l
         ) => MonoSub F r l 
{-
    where
    monosub _ r = (mono' r)

-}

class Emptyword r b | r -> b 
{-
    where
    emptyword :: r -> b
-}
-- For PHI
instance Emptyword PHI F

instance Emptyword EMPT T 
{-
    where
    emptyword _ = T
-}

instance Emptyword (LAB l) F 
{-
    where
    emptyword _ = F
-}

instance ( Emptyword r1 b'
	 , AndEmptyword b' r2 b
	 ) => Emptyword (r1,r2) b 
{-    
    where
    emptyword (r1,r2) = andemptyword (emptyword r1) r2
-}

instance ( Emptyword r1 b'
	 , OrEmptyword b' r2 b
	 ) => Emptyword (OR r1 r2) b 
{-    
    where
    emptyword (OR r1 r2) = oremptyword (emptyword r1) r2 
-}

instance Emptyword (STAR r) T 
{-
    where
    emptyword _ = T
-}
-- two auxiliary classes
class AndEmptyword b1 r b2 | b1 r -> b2 
{-    
    where
    andemptyword :: b1 -> r -> b2
-}

instance (Emptyword r b) => AndEmptyword T r b 
{-
    where
    andemptyword _ r = emptyword r
-}

instance AndEmptyword F r F 
{-    
    where
    andemptyword F _ = F
-}

class OrEmptyword b1 r b2 | b1 r -> b2 
{-
    where
    oremptyword :: b1 -> r -> b2
-}

instance OrEmptyword T r T 
{-
    where
    oremptyword T _ = T
-}

instance (Emptyword r b) => OrEmptyword F r b 
{-
    where
    oremptyword F r = emptyword r
-}

class Mono' r l | r -> l 
{-
    where
    mono' :: r -> l 
-}
-- For PHI
instance Mono' PHI XHaskell.RETypes.N

instance Mono' EMPT XHaskell.RETypes.N 
{-    
    where
    mono' EMPT = XHaskell.RETypes.N
-}

instance Mono' (LAB l) (XHaskell.RETypes.C ((LAB l),EMPT) XHaskell.RETypes.N) 
{-
    where
    mono' (LAB l) = XHaskell.RETypes.C ((LAB l),EMPT) XHaskell.RETypes.N
-}

instance ( Mono'' r (STAR r) l
         ) => Mono' (STAR r) l 
{-
    where
    mono' (STAR r) = mono'' r (STAR r)
-}

instance ( Mono' r1 l1
         , Mono' r2 l2
         , Append l1 l2 l3
         ) => Mono' (OR r1 r2) l3 
{-    
    where
    mono' (OR r1 r2) = append (mono' r1) (mono' r2)
-}

-- for PHI
instance Mono' (PHI,r) N
          

instance ( Mono' r1 l2
         ) => Mono' (EMPT,r1) l2 
{-
    where
    mono' (EMPT,r1) = mono' r1
-}

instance Mono' ((LAB l),r1) (XHaskell.RETypes.C ((LAB l),r1) N) 
{-    
    where
    mono' ((LAB l),r1) = XHaskell.RETypes.C ((LAB l),r1) N
-}

instance ( Mono' (r1,(r2,r3)) l
         ) => Mono' ((r1,r2),r3) l 
{-
    where
    mono' ((r1,r2),r3) = mono' (r1,(r2,r3))
-}
instance ( Mono' (OR (r1,r3) (r2,r3)) l
         ) => Mono' ((OR r1 r2),r3) l 
{-    
    where
    mono' ((OR r1 r2),r3) = mono' (OR (r1,r3) (r2,r3))
-}

instance ( Mono'' (STAR r1) r2 l1
         , Mono' r2 l2
         , Append l1 l2 l3
-- only needed in GHC 6.2
         , Mono'' r1 (STAR r1, r2) l1
         ) => Mono' ((STAR r1),r2) l3 
{-
    where
    mono' ((STAR r1),r2) = append (mono'' (STAR r1) r2) (mono' r2)
-}

class Mono'' r1 r2 l | r1 r2 -> l 
{-
    where
    mono'' :: r1 -> r2 -> l
-}

instance Mono'' EMPT r XHaskell.RETypes.N 
{-    
    where
    mono'' _ _ = XHaskell.RETypes.N
-}
instance Mono'' (LAB l) r (XHaskell.RETypes.C ((LAB l),r) XHaskell.RETypes.N) 
{-    
    where
    mono'' (LAB l) r = XHaskell.RETypes.C ((LAB l),r) XHaskell.RETypes.N
-}

instance ( Mono'' r1 ((STAR r1),r2) l
         ) => Mono'' (STAR r1) r2 l 
{-
    where
    mono'' (STAR r1) r2 = mono'' r1 ((STAR r1),r2)
-}

instance ( Mono'' r1 r3 l1
         , Mono'' r2 r3 l2
         , Append l1 l2 l3
         ) => Mono'' (OR r1 r2) r3 l3 
{-
    where
    mono'' (OR r1 r2) r3 = append (mono'' r1 r3) (mono'' r2 r3)
-}

instance ( Mono'' r1 r2 l
         ) => Mono'' (EMPT,r1) r2 l 
{-
    where
    mono'' (EMPT,r1) r2 = mono'' r1 r2
-}

instance Mono'' ((LAB l),r1) r2 (XHaskell.RETypes.C ((LAB l),(r1,r2)) XHaskell.RETypes.N) 
{-
    where
    mono'' ((LAB l),r1) r2 = XHaskell.RETypes.C ((LAB l),(r1,r2)) XHaskell.RETypes.N
-}

instance ( Mono'' (r1,(r2,r3)) r4 l
         ) => Mono'' ((r1,r2),r3) r4 l 
{-
    where
    mono'' ((r1,r2),r3) r4 = mono'' (r1,(r2,r3)) r4
-}

instance ( Mono'' (OR (r1,r3) (r2,r3)) r4 l
         ) => Mono'' ((OR r1 r2),r3) r4 l 
{-
    where
    mono'' ((OR r1 r2),r3) r4 = mono'' (OR (r1,r3) (r2,r3)) r4
-}

instance ( Mono'' (STAR r1) (r2,r3) l1
         , Mono'' r2 r3 l2
         , Append l1 l2 l3
-- only needed in GHC 6.2
         , Mono'' r1 (STAR r1, (r2, r3)) l1
         ) => Mono'' ((STAR r1),r2) r3 l3 
{-
    where
    mono'' ((STAR r1),r2) r3 = append (mono'' (STAR r1) (r2,r3)) (mono'' r2 r3)
-}


class Sort l1 l2 | l1 -> l2 
{-
    where
    sort :: l1 -> l2
-}

instance Sort XHaskell.RETypes.N XHaskell.RETypes.N 
{-
    where
    sort XHaskell.RETypes.N = XHaskell.RETypes.N
-}
instance ( Sort ms ms'
         , Insert m ms' ms''
         ) => Sort (XHaskell.RETypes.C m ms) ms'' 
{-
    where
    sort (XHaskell.RETypes.C m ms) = insert m (sort ms)
-}


class Insert m ms ms' | m ms -> ms' 
{-
    where
    insert :: m -> ms -> ms'
-}

instance Insert m XHaskell.RETypes.N (XHaskell.RETypes.C m XHaskell.RETypes.N) 
{-
    where
    insert m XHaskell.RETypes.N = XHaskell.RETypes.C m XHaskell.RETypes.N
-}

-- require a syntatic merge to handle case like, Norm (A*,A*)
-- instance Insert ((LAB l),r) (XHaskell.RETypes.C ((LAB l),r') ms) (XHaskell.RETypes.C ((LAB l),(OR r r')) ms) 
-- TODO: continue with the proof terms
instance ( SMerge r r' r''
         ) => Insert ((LAB l),r) (XHaskell.RETypes.C ((LAB l),r') ms) (XHaskell.RETypes.C ((LAB l),r'') ms) 
{-
    where
    insert (l,r) (XHaskell.RETypes.C (_,r') ms) = XHaskell.RETypes.C (l,(OR r r')) ms
-}

instance ( M2N m1 n1
	 , M2N m2 n2
	 , LeqT n1 n2 b
	 , Insert2 b m1 (XHaskell.RETypes.C m2 ms) ms'
	 ) => Insert m1 (XHaskell.RETypes.C m2 ms) ms' 
{-
    where
    insert m1 (XHaskell.RETypes.C m2 ms) = 
	insert2 (leqT (m2n m1) (m2n m2)) m1 (XHaskell.RETypes.C m2 ms)
-}


class Insert2 b m1 l1 l2 | b m1 l1 -> l2 
{-
    where
    insert2 :: b -> m1 -> l1 -> l2
-}
instance Insert2 T m l (XHaskell.RETypes.C m l)
{-
    where
    insert2 T m l = XHaskell.RETypes.C m l
-}
instance ( Insert m1 l2 l3
	 ) => Insert2 F m1 (XHaskell.RETypes.C m2 l2) (XHaskell.RETypes.C m2 l3) 
{-
    where
    insert2 F m1 (XHaskell.RETypes.C m2 l2) = XHaskell.RETypes.C m2 (insert m1 l2)
-}

class Lnf l r | l -> r 
{-
    where
    lnf :: l -> r 
-}

instance Lnf XHaskell.RETypes.N PHI 
{-
    where
    lnf XHaskell.RETypes.N = PHI
-}

instance ( Lnf ms r
         ) => Lnf (XHaskell.RETypes.C m ms) (OR m r) 
{-
    where
    lnf (XHaskell.RETypes.C m ms) = OR m (lnf ms)
-}

-- TODO: need to check that whether this set of rules is complete and implenetable in terms of proof terms.
class SMerge r1 r2 r3  | r1 r2 -> r3

instance (EQ r r') => SMerge r r r'

instance (EQ r'' (OR r r')) => SMerge r (OR r r') r''

instance (SMerge r r'' r''') => SMerge r (OR r' r'') (OR r' r''')

instance (EQ r'' (OR r r')) => SMerge r r' r''


class EQ r s | r -> s, s -> r

instance EQ r r


class LeqT n1 n2 b | n1 n2 -> b 
    where
    leqT :: n1 -> n2 -> b


instance LeqT Z n T where
    leqT Z _ = T

instance LeqT (S n) Z F where
    leqT (S _) Z = F

instance ( LeqT n1 n2 b
	 ) => LeqT (S n1) (S n2) b where
    leqT (S n1) (S n2) = leqT n1 n2




class Append l1 l2 l3 | l1 l2 -> l3 where
    append :: l1 -> l2 -> l3 

instance Append XHaskell.RETypes.N l l where
    append XHaskell.RETypes.N l = l

instance ( Append xs l l'
         ) => Append (XHaskell.RETypes.C x xs) l (XHaskell.RETypes.C x l') where
    append (XHaskell.RETypes.C x xs) l = XHaskell.RETypes.C x (append xs l)


class M2N r n | r -> n where
    m2n :: r -> n


-- chameleon does not support class and instance being declared in seperate files.
data A = A 
--         deriving Show

data B = B
--         deriving Show

data C = C
--         deriving Show

data BR = BR -- the "Break" literal

instance M2N ((LAB A),r) Z
    where
    m2n _ = Z

instance M2N ((LAB B),r) (S Z) 
    where
    m2n _ = S Z

instance M2N ((LAB XHaskell.RENorm.C),r) (S (S Z)) 
    where
    m2n _ = S (S Z)

instance M2N ((LAB BR),r) (S (S (S Z)))
    where
    m2n _ = S (S (S Z))


instance M2N EMPT (S (S (S (S Z))))
    where
    m2n _ = S (S (S (S Z)))


