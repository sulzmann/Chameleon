module XHaskell.REOpts where

-- all regular expression operations like intersect, diff, left quotient and right quotient and others.

import XHaskell.RETypes
import XHaskell.RENorm --(Norm,A,B)
-- need to rewrite the FD using Martin's trick

-- We need two more succ for generating fresh variable
data SL n = SL n
data SR n = SR n

------------------------------------Intersection ---------------------------------------

class ISect r1 r2 r3 | r1 r2 -> r3

instance (IsToGr N Z r1 r2 g, GrToRe g Z r, Simplify r r3) => ISect r1 r2 r3


------------------------------------Intersection to grammar-----------------------------
-- g = input grammar, v = variable, r1 r2 , g' = output grammar
-- in the input grammar, x -> (R1 \isect R2) is represented as (x,(R1,R2))
-- Variables are represented by numbers.

class IsToGr g v r1 r2 g' | g v r1 r2 -> g'

instance ( RHSIn r1 r2 g b
         , IsToGrSub b g x r1 r2 g'
         ) => IsToGr g x r1 r2 g'

-- b = boolean type
class IsToGrSub b g v r1 r2 g' | b g v r1 r2 -> g'

instance ( GLookUp r1 r2 g y
         ) => IsToGrSub T g x r1 r2 (XHaskell.RETypes.C (x,y) N)

instance ( Norm r1 n1
         , Norm r2 n2
         , NIsToGr (XHaskell.RETypes.C (x,(r1,r2)) g) (S x) n1 n2 g'
         ) => IsToGrSub F g x r1 r2 (XHaskell.RETypes.C (x,(S x)) g')


class NIsToGr g v n1 n2 g' | g v n1 n2 -> g'

instance NIsToGr g x PHI n (XHaskell.RETypes.C (x,PHI) N)

instance NIsToGr g x n PHI (XHaskell.RETypes.C (x,PHI) N)

instance ( NIsToGr g (S x) n1 n2 g'
         ) => NIsToGr g x (OR EMPT n1) (OR EMPT n2) (XHaskell.RETypes.C (x,(OR EMPT (S x))) g')


instance ( IsToGr g (SL x) r1 r2 g'
         , NIsToGr g (SR x) n1 n2 g''
         , Append g' g'' g'''
         ) => NIsToGr g x (OR ((LAB l),r1) n1) (OR ((LAB l),r2) n2) (XHaskell.RETypes.C (x,(OR ((LAB l),(SL x)) (SR x))) g''')

instance ( M2N m1 i1
         , M2N m2 i2
         , LeqT i1 i2 b
         , NIsToGrSub b g x (OR m1 n1) (OR m2 n2) g'
         ) => NIsToGr g x (OR m1 n1) (OR m2 n2) g'

class NIsToGrSub b g x n1 n2 g' | b g x n1 n2 -> g'


instance ( NIsToGr g (S x) n1 (OR m2 n2) g'
         ) => NIsToGrSub T g x (OR m1 n1) (OR m2 n2) (XHaskell.RETypes.C (x,(S x)) g')

instance ( NIsToGr g (S x) (OR m1 n1) n2 g'
         ) => NIsToGrSub F g x (OR m1 n1) (OR m2 n2) (XHaskell.RETypes.C (x,(S x)) g')

------------------------------------Difference ---------------------------------------

class Diff r1 r2 r3 | r1 r2 -> r3

instance (DfToGr N Z r1 r2 g, GrToRe g Z r, Simplify r r3) => Diff r1 r2 r3

------------------------------Difference To Grammar ----------------------------------

class DfToGr g v r1 r2 g' | g v r1 r2 -> g'

instance ( RHSIn r1 r2 g b
         , DfToGrSub b g v r1 r2 g'
         ) => DfToGr g v r1 r2 g'

class DfToGrSub b g v r1 r2 g' | b g v r1 r2 -> g'

instance ( GLookUp r1 r2 g y
         ) => DfToGrSub T g x r1 r2 (XHaskell.RETypes.C (x,y) N)

instance ( Norm r1 n1
         , Norm r2 n2
         , NDfToGr (XHaskell.RETypes.C (x,(r1,r2)) g) (S x) n1 n2 g'
         ) => DfToGrSub F g x r1 r2 (XHaskell.RETypes.C (x,(S x)) g')


class NDfToGr g v n1 n2 g' | g v n1 n2 -> g'

instance NDfToGr g x PHI n (XHaskell.RETypes.C (x,PHI) N)

instance NDfToGr g x n PHI (XHaskell.RETypes.C (x,n) N)

instance ( NDfToGr g (S x) n1 n2 g'
         ) => NDfToGr g x (OR EMPT n1) (OR EMPT n2) (XHaskell.RETypes.C (x,(S x)) g')

instance ( DfToGr g (SL x) r1 r2 g'
         , NDfToGr g (SR x) n1 n2 g''
         , Append g' g'' g'''
         ) => NDfToGr g x (OR ((LAB l),r1) n1) (OR ((LAB l),r2) n2) (XHaskell.RETypes.C (x,(OR ((LAB l),(SL x)) (SR x))) g''')

instance ( M2N m1 i1
         , M2N m2 i2
         , LeqT i1 i2 b
         , NDfToGrSub b g x (OR m1 n1) (OR m2 n2) g'
         ) => NDfToGr g x (OR m1 n1) (OR m2 n2) g'

class NDfToGrSub b g x n1 n2 g' | b g x n1 n2 -> g'


instance ( NDfToGr g (S x) n1 (OR m2 n2) g'
         ) => NDfToGrSub T g x (OR m1 n1) (OR m2 n2) (XHaskell.RETypes.C (x,(OR m1 (S x))) g')

instance ( NDfToGr g (S x) (OR m1 n1) n2 g'
         ) => NDfToGrSub F g x (OR m1 n1) (OR m2 n2) (XHaskell.RETypes.C (x,(S x)) g')

------------------------------------Left-Quotient ---------------------------------------

class LQuo r1 r2 r3 | r1 r2 -> r3

instance (LqToGr N Z r1 r2 g, GrToRe g Z r, Simplify r r3) => LQuo r1 r2 r3

------------------------------Left-Quotient To Grammar ----------------------------------

class LqToGr g v r1 r2 g' | g v r1 r2 -> g'

instance ( RHSIn r1 r2 g b
         , LqToGrSub b g v r1 r2 g'
         ) => LqToGr g v r1 r2 g'

class LqToGrSub b g v r1 r2 g' | b g v r1 r2 -> g'

instance ( GLookUp r1 r2 g y
         ) => LqToGrSub T g x r1 r2 (XHaskell.RETypes.C (x,y) N)

instance ( Norm r1 n1
         , Norm r2 n2
         , NLqToGr (XHaskell.RETypes.C (x,(r1,r2)) g) (S x) n1 n2 g'
         ) => LqToGrSub F g x r1 r2 (XHaskell.RETypes.C (x,(S x)) g')


class NLqToGr g v n1 n2 g' | g v n1 n2 -> g'

instance NLqToGr g x PHI n (XHaskell.RETypes.C (x,PHI) N)

instance NLqToGr g x n PHI (XHaskell.RETypes.C (x,PHI) N)

instance NLqToGr g x EMPT n2 (XHaskell.RETypes.C (x,n2) N)

instance ( LqToGr g (S x) r1 r2 g'
         ) => NLqToGr g x ((LAB l),r1) (OR ((LAB l),r2) n2) (XHaskell.RETypes.C (x,(S x)) g')

instance ( M2N ((LAB l1),r1) i1
         , M2N m2 i2
         , LeqT i1 i2 b
         , NLqToGrSub b g x ((LAB l1),r1) (OR m2 n2) g'
         ) => NLqToGr g x ((LAB l1),r1) (OR m2 n2) g'

instance ( NLqToGr g (SL x) m1 n2 g'
         , NLqToGr g (SR x) n1 n2 g''
         , Append g' g'' g'''
         ) => NLqToGr g x (OR m1 n1) n2 (XHaskell.RETypes.C (x,(OR (SL x) (SR x))) g''')

class NLqToGrSub b g x n1 n2 g' | b g x n1 n2 -> g'


instance NLqToGrSub T g x ((LAB l1),r1) (OR m2 n2) (XHaskell.RETypes.C (x,PHI) N)

instance ( NLqToGr g (S x) ((LAB l1),r1) n2 g'
         ) => NLqToGrSub F g x ((LAB l1),r1) (OR m2 n2) (XHaskell.RETypes.C (x,(S x)) g')


--------------------------Right-Quotient----------------------------------------
class RQuo r1 r2 r3 | r1 r2 -> r3

instance ( Reverse r1 rr1
         , Reverse r2 rr2
         , LQuo rr2 rr1 rr3
         , Reverse rr3 r3
         ) => RQuo r1 r2 r3

---------------------------Reversal --------------------------------------------

class Reverse r rr | r -> rr

instance Reverse PHI PHI

instance Reverse EMPT EMPT

instance Reverse (LAB l) (LAB l)

instance ( Reverse r1 rr1
         , Reverse r2 rr2
         ) => Reverse (r1,r2) (rr2,rr1)

instance ( Reverse r1 rr1
         , Reverse r2 rr2
         ) => Reverse (OR r1 r2) (OR rr1 rr2)

instance ( Reverse r rr
         ) => Reverse (STAR r) (STAR rr)

--------------------------Grammar to Regular Expression-------------------------
--Currently this is not efficient.
class GrToRe g x r | g x -> r 


instance ( GLookUpRHS x g r'    -- r' = g(x)
         , RHSFv r' l           -- l = fv(r')
         , FvsGt l x l'         -- get all variables that are greater than x
         , MGrToRe g l' lr      -- get all solutions for each v in l' obtaining lr
         , ApplySubs r' l' lr r'' -- substitute all variables in r' with [v/r] for all v in l' and r in lr 
         , RHSHas x r'' b        -- check whether it contains a recursion
         , GrToReSub b x r'' r''' -- subprocedure: if there no recursion, keep it, if not reduce.
         ) => GrToRe g x r'''


class GrToReSub b x r r' | b x r -> r'

instance GrToReSub F x r r

instance (RmRec x r r' ) => GrToReSub T x r r'

-- Removing Recursion
class RmRec x r r' | x r -> r' --asssume r is in LNF

{-
instance ( RmRecSub x r (l,m)
         ) => RmRec x r ((STAR l),m)
-}
instance ( RmRecSub x r (l,m)
         , IsPhi l b
         , IsPhi m b'
         , RmRec' b b' x r l m r'
         ) => RmRec x r r'

class RmRec' b b' x r l m r' | b b' x r l m -> r' 

instance RmRec' T T x r l m PHI

instance RmRec' F T x r l m PHI

instance RmRec' T F x r l m r

instance RmRec' F F x r l m ((STAR l),m) 

class RmRecSub x r ls | x r -> ls

instance RmRecSub x PHI (PHI,PHI)

instance RmRecSub x EMPT (PHI,EMPT)

instance RmRecSub x (LAB l) (PHI,(LAB l))

instance ( RmRecSub x r' (l,m)
         ) => RmRecSub x (r,r') ((r,l),(r,m)) -- r must be either label or star

instance ( RmRecSub x r1 (l1,m1)
         , RmRecSub x r2 (l2,m2)
         ) => RmRecSub x (OR r1 r2) ((OR l1 l2),(OR m1 m2))

instance ( Equal x Z b
         , RmRecSubSub b x Z (l,m)
         ) => RmRecSub x Z (l,m)

instance ( Equal x (S n) b
         , RmRecSubSub b x (S n) (l,m)
         ) => RmRecSub x (S n) (l,m)

instance ( Equal x (SL n) b
         , RmRecSubSub b x (SL n) (l,m)
         ) => RmRecSub x (SL n) (l,m)

instance ( Equal x (SR n) b
         , RmRecSubSub b x (SR n) (l,m)
         ) => RmRecSub x (SR n) (l,m)

-- only needed for LQuo
instance RmRecSub x (STAR r) (PHI,(STAR r))


class RmRecSubSub b x y ls | b x y -> ls

instance RmRecSubSub T x y (EMPT,PHI)

instance RmRecSubSub F x y (PHI,y)



-- Map GrToRe over a list of vars
class MGrToRe g l lr | g l -> lr 

instance MGrToRe g XHaskell.RETypes.N XHaskell.RETypes.N 

instance ( GrToRe g x r
         , MGrToRe g xs rs
         ) => MGrToRe g (XHaskell.RETypes.C x xs) (XHaskell.RETypes.C r rs)



------------------- Pi Function and Inverse Function --------------------------
class IPI r r' | r -> r'

instance IPI PHI PHI

instance IPI EMPT (OR EMPT (LAB BR))

instance IPI (LAB l) ((OR EMPT (LAB BR)),((LAB l),(OR EMPT (LAB BR))))

instance ( IPI r1 r1'
         , IPI r2 r2'
         ) => IPI (r1,r2) (r1',((OR (LAB BR) EMPT),r2'))

instance ( IPI r1 r1'
         , IPI r2 r2'
         ) => IPI (OR r1 r2) (OR r1' r2')

instance ( IPI r r'
         ) => IPI (STAR r) (STAR (OR r' (LAB BR)))

-- do we need this?
class PI r r' | r -> r'

instance PI PHI PHI

instance PI EMPT EMPT

instance (EQ EMPT r) => PI (LAB BR) r

instance (EQ (LAB l) r) => PI (LAB l) r

instance (PI r1 r1', PI r2 r2') => PI (r1,r2) (r1',r2')

instance (PI r1 r1', PI r2 r2') => PI (OR r1 r2) (OR r1' r2')

instance (PI r r') => PI (STAR r) (STAR r')

------------------- Break, LBreak and RBreak ---------------------------------
-- c : input language, l1 : left componet, l2 : right compent, o : output
class Break c l1 l2 o | c l1 l2 -> o

instance ( IPI l1 l1'                           -- Pi-1(L1)
         , Diff l1' (l1,(LAB BR)) a             -- A
         , IPI c c'                             -- Pi-1(C)
         , Diff (l1,((LAB BR),l2)) (a,l2) l'    -- (L1,BR,L2) - (A,L2)
         , ISect c' l' o
         ) => Break c l1 l2 o

class LBreak c l1 l2 o | c l1 l2 -> o
instance ( Break c l1 l2 o'
         , RQuo o' ((LAB BR),l2) o
         ) => LBreak c l1 l2 o

class RBreak c l1 l2 o | c l1 l2 -> o
instance ( Break c l1 l2 o'
         , LQuo (l1,(LAB BR)) o' o
         ) => RBreak c l1 l2 o

------------------- simplify a regular expression------------------------------
-- simplify a regular exression to a sub-minimal form.

class Simplify r s | r -> s 
{-
instance ( Simplify' r r'
         , Reverse r' rr'
         , Simplify' r'' rs
         , Reverse rs s
         ) => Simplify r s

class Simplify' r s | r -> s
-}

instance Simplify PHI PHI

instance Simplify EMPT EMPT

instance Simplify (LAB l) (LAB l)

instance ( Simplify r r''
         , SimplifySTAR r'' (STAR r) r'
         ) => Simplify (STAR r) r'

instance ( Simplify r1 r1'
         , Simplify r2 r2'
         , SimplifyPAIR r1' r2' r
         ) => Simplify (r1,r2) r

instance ( Simplify r1 r1'
         , Simplify r2 r2'
         , SimplifyOR r1' r2' r
         ) => Simplify (OR r1 r2) r

class SimplifySTAR r1 r2 r3 | r1 r2 -> r3

instance SimplifySTAR PHI (STAR r) EMPT

instance SimplifySTAR (LAB l) (STAR r) (STAR (LAB l))

instance SimplifySTAR EMPT (STAR r) EMPT

instance SimplifySTAR (r1,r2) (STAR r) (STAR (r1,r2))

instance SimplifySTAR (OR r1 r2) (STAR r) (STAR (OR r1 r2))

instance SimplifySTAR (STAR r') (STAR r) (STAR r')

class SimplifyPAIR r1 r2 r | r1 r2 -> r

instance SimplifyPAIR PHI r PHI

instance SimplifyPAIR EMPT r r

instance SimplifyPAIR (LAB l) PHI PHI

instance SimplifyPAIR (LAB l) EMPT (LAB l)

instance SimplifyPAIR (LAB l) (LAB l') ((LAB l),(LAB l'))

instance SimplifyPAIR (LAB l) (OR r1 r2) ((LAB l),(OR r1 r2))

instance SimplifyPAIR (LAB l) (r1,r2) ((LAB l),(r1,r2))

instance SimplifyPAIR (LAB l) (STAR r) ((LAB l),(STAR r))

instance SimplifyPAIR (r1,r2) PHI PHI

instance SimplifyPAIR (r1,r2) EMPT (r1,r2)

instance SimplifyPAIR (r1,r2) (LAB l) (r1,(r2,(LAB l)))

instance SimplifyPAIR (r1,r2) (r1',r2') (r1,(r2,(r1',r2')))

instance SimplifyPAIR (r1,r2) (OR r1' r2') (r1,(r2,(OR r1' r2')))

instance SimplifyPAIR (r1,r2) (STAR r) (r1,(r2,(STAR r)))

instance SimplifyPAIR (STAR r) PHI PHI

instance SimplifyPAIR (STAR r) EMPT (STAR r)

instance SimplifyPAIR (STAR r) (LAB l) ((STAR r),(LAB l))

instance SimplifyPAIR (STAR r) (r1,r2) ((STAR r),(r1,r2))

instance SimplifyPAIR (STAR r) (OR r1 r2) ((STAR r),(OR r1 r2))

instance SimplifyPAIR (STAR r) (STAR r') ((STAR r),(STAR r'))

instance SimplifyPAIR (OR r1 r2) PHI PHI

instance SimplifyPAIR (OR r1 r2) EMPT (OR r1 (OR r2 EMPT))
instance SimplifyPAIR (OR r1 r2) (LAB l) (OR r1 (OR r2 (LAB l)))
instance SimplifyPAIR (OR r1 r2) (r1',r2') (OR r1 (OR r2 (r1',r2')))
instance SimplifyPAIR (OR r1 r2) (OR r1' r2') (OR r1 (OR r2 (OR r1' r2')))
instance SimplifyPAIR (OR r1 r2) (STAR r3) (OR r1 (OR r2 (STAR r3)))

class SimplifyOR r1 r2 r | r1 r2 -> r

instance SimplifyOR PHI r r

instance SimplifyOR EMPT PHI EMPT

instance SimplifyOR EMPT EMPT EMPT

instance SimplifyOR EMPT (LAB l) (OR EMPT (LAB l))

instance SimplifyOR EMPT (OR r1 r2) (OR EMPT (OR r1 r2))

instance SimplifyOR EMPT (r1,r2) (OR EMPT (r1,r2))

instance SimplifyOR EMPT (STAR r) (STAR r)

instance SimplifyOR (LAB l) PHI (LAB l)

instance SimplifyOR (LAB l) EMPT (OR (LAB l) EMPT)

instance SimplifyOR (LAB l) (LAB l') (OR (LAB l) (LAB l'))

instance SimplifyOR (LAB l) (OR r1 r2) (OR (LAB l) (OR r1 r2))

instance SimplifyOR (LAB l) (r1,r2) (OR (LAB l) (r1,r2))

instance SimplifyOR (LAB l) (STAR r) (OR (LAB l) (STAR r))

instance SimplifyOR (r1,r2) PHI (r1,r2)

instance SimplifyOR (r1,r2) EMPT (OR (r1,r2) EMPT)

instance SimplifyOR (r1,r2) (LAB l) (OR (r1,r2) (LAB l))

instance SimplifyOR (r1,r2) (r1',r2') (OR (r1,r2) (r1',r2'))

instance SimplifyOR (r1,r2) (OR r1' r2') (OR (r1,r2) (OR r1' r2'))

instance SimplifyOR (r1,r2) (STAR r) (OR (r1,r2) (STAR r))

instance SimplifyOR (STAR r) PHI (STAR r)

instance SimplifyOR (STAR r) EMPT (STAR r)

instance SimplifyOR (STAR r) (LAB l) (OR (STAR r) (LAB l))

instance SimplifyOR (STAR r) (r1,r2) (OR (STAR r) (r1,r2))

instance SimplifyOR (STAR r) (OR r1 r2) (OR (STAR r) (OR r1 r2))

instance SimplifyOR (STAR r) (STAR r') (OR (STAR r) (STAR r'))

instance SimplifyOR (OR r1 r2) PHI (OR r1 r2)

instance SimplifyOR (OR r1 r2) EMPT (OR (OR r1 r2) EMPT)
instance SimplifyOR (OR r1 r2) (LAB l) (OR (OR r1 r2) (LAB l))
instance SimplifyOR (OR r1 r2) (r1',r2') (OR (OR r1 r2) (r1',r2'))
instance SimplifyOR (OR r1 r2) (OR r1' r2') (OR (OR r1 r2) (OR r1' r2'))
instance SimplifyOR (OR r1 r2) (STAR r3) (OR (OR r1 r2) (STAR r3))


----------------------------------Auxillary Functions-------------------------------
-- checks whether (r1,r2) is the rhs of some production in grammar g.
class RHSIn r1 r2 g b | r1 r2 g -> b 

instance RHSIn r1 r2 N F

-- *NOTE: This can be improved by (r \isect s) = (s \isect r) but not for \diff*
instance RHSIn r1 r2 (XHaskell.RETypes.C (v,(r1,r2)) gs) T  

instance (RHSIn r1 r2 gs b) => RHSIn r1 r2 (XHaskell.RETypes.C (v,rs) gs) b

-- checks the RHS contains a particular variable
class RHSHas x r b | x r -> b

instance RHSHas x PHI F

instance RHSHas x EMPT F

instance RHSHas x (LAB l) F

instance ( RHSHas x r1 b
         , OrRHSHas b x r2 b'
         ) => RHSHas x (r1,r2) b'

instance ( RHSHas x r1 b
         , OrRHSHas b x r2 b'
         ) => RHSHas x (OR r1 r2) b'

instance (RHSHas x r b) => RHSHas x (STAR r) b

-- If free, I need to find out why this doesn't work. :-(

-- instance (Equal x r b) => RHSHas x r b

-- I made it more specific 

instance (Equal x Z b) => RHSHas x Z b

instance (Equal x (S n) b) => RHSHas x (S n) b

instance (Equal x (SR n) b) => RHSHas x (SR n) b

instance (Equal x (SL n) b) => RHSHas x (SL n) b



class OrRHSHas b x r b' | b x r -> b'

instance OrRHSHas T x r T

instance (RHSHas x r b) => OrRHSHas F x r b


-- looks up the correspondent non-terminal x such that x -> (r1 \isect r2) \in g
class GLookUp r1 r2 g v | r1 r2 g -> v

instance GLookUp r1 r2 (XHaskell.RETypes.C (v,(r1,r2)) gs) v

instance (GLookUp r1 r2 gs v') => GLookUp r1 r2 (XHaskell.RETypes.C (v,rs) gs) v'



-- looks up the correspondent RHS such that x -> RHS \in g
class GLookUpRHS x g r | x g -> r

instance GLookUpRHS x (XHaskell.RETypes.C (x,r) gs) r

instance (GLookUpRHS x gs r) => GLookUpRHS x (XHaskell.RETypes.C (y,rs) gs) r


-- apply a set of substution on rhs 

class ApplySubs r v e r' | r v e -> r'

instance ApplySubs r XHaskell.RETypes.N e r

instance ( ApplySub r v e r1
         , ApplySubs r1 vs es r'
         ) => ApplySubs r (XHaskell.RETypes.C v vs) (XHaskell.RETypes.C e es) r' 

-- apply one substitution on rhs
class ApplySub r v e r' | r v e -> r'

instance ApplySub PHI v e PHI

instance ApplySub EMPT v e EMPT

instance ApplySub (LAB l) v e (LAB l) 

instance ( ApplySub r1 v e r1'
         , ApplySub r2 v e r2'
         ) => ApplySub (r1,r2) v e (r1',r2')

instance ( ApplySub r1 v e r1'
         , ApplySub r2 v e r2'
         ) => ApplySub (OR r1 r2) v e (OR r1' r2')

instance ( ApplySub r v e r'
         ) => ApplySub (STAR r) v e (STAR r')
{-
instance ( Equal r v b
         , ApplySubSub b r e r'
         ) => ApplySub r v e r' 
-}

instance ( Equal Z v b
         , ApplySubSub b Z e r'
         ) => ApplySub Z v e r' 
instance ( Equal (S r) v b
         , ApplySubSub b (S r) e r'
         ) => ApplySub (S r) v e r' 
instance ( Equal (SR r) v b
         , ApplySubSub b (SR r) e r'
         ) => ApplySub (SR r) v e r' 
instance ( Equal (SL r) v b
         , ApplySubSub b (SL r) e r'
         ) => ApplySub (SL r) v e r' 


class ApplySubSub b r e r' | b r e -> r'

instance ApplySubSub T r e e

instance ApplySubSub F r e r


-- returns the list of free variable in the RHS
class RHSFv r vs | r -> vs

instance RHSFv PHI N

instance RHSFv EMPT N

instance RHSFv Z (XHaskell.RETypes.C Z N)

instance RHSFv (S n) (XHaskell.RETypes.C (S n) N)

instance RHSFv (SL n) (XHaskell.RETypes.C (SL n) N)

instance RHSFv (SR n) (XHaskell.RETypes.C (SR n) N)

instance RHSFv (LAB l) N

instance ( RHSFv r1 l1
         , RHSFv r2 l2
         , Append l1 l2 l3
         ) => RHSFv (r1,r2) l3

instance ( RHSFv r1 l1
         , RHSFv r2 l2
         , Append l1 l2 l3
         ) => RHSFv (OR r1 r2) l3

instance ( RHSFv r l
         ) => RHSFv (STAR r) l


-- Get a list of variable greater than the current one

class FvsGt l x l' | l x -> l'

instance FvsGt XHaskell.RETypes.N x XHaskell.RETypes.N

instance ( Gt y x b
         , FvsGtSub b (XHaskell.RETypes.C y ys) x zs
         ) => FvsGt (XHaskell.RETypes.C y ys) x zs

class FvsGtSub b l x l' | b l x -> l'

instance ( FvsGt ys x ys'
         ) => FvsGtSub T (XHaskell.RETypes.C y ys) x (XHaskell.RETypes.C y ys')

instance ( FvsGt ys x ys'
         ) => FvsGtSub F (XHaskell.RETypes.C y ys) x ys'


-- Compare two variables to see whether the first one is greater than the second one.
-- the current implementation is  naive: just counting the length of the S and Z sequence
class Gt y x b | y x -> b

instance Gt Z Z F

instance Gt Z (S n) F

instance Gt Z (SL n) F

instance Gt Z (SR n) F

instance Gt (S n) Z T

instance (Gt n n' b) => Gt (S n) (S n') b

instance (Gt n n' b) => Gt (S n) (SL n') b

instance (Gt n n' b) => Gt (S n) (SR n') b

instance Gt (SL n) Z T

instance (Gt n n' b) => Gt (SL n) (SL n') b

instance (Gt n n' b) => Gt (SL n) (S n') b

instance (Gt n n' b) => Gt (SL n) (SR n') b

instance Gt (SR n) Z T

instance (Gt n n' b) => Gt (SR n) (SR n') b

instance (Gt n n' b) => Gt (SR n) (SL n') b

instance (Gt n n' b) => Gt (SR n) (S n') b 

-- Compare two variables to see whether the first one is equal than the second one.

class Equal y x b | y x -> b

instance Equal x x T

instance Equal Z (S n) F

instance Equal Z (SL n) F

instance Equal Z (SR n) F

instance (Equal n n' b) => Equal (S n) (S n') b

instance Equal (S n) Z F

instance Equal (S n) (SL n') F

instance Equal (S n) (SR n') F

instance (Equal n n' b) => Equal (SL n) (SL n') b

instance Equal (SL n) Z F

instance Equal (SL n) (S n') F

instance Equal (SL n) (SR n') F

instance (Equal n n' b) => Equal (SR n) (SR n') b

instance Equal (SR n) Z F

instance Equal (SR n) (SL n') F

instance Equal (SR n) (S n') F

class IsPhi r b | r -> b
-- very naive implementation of empty language testing.

instance IsPhi PHI T

instance IsPhi EMPT F

instance IsPhi (LAB l) F

instance IsPhi (STAR r) F

instance IsPhi (r1,r2) F

instance IsPhi (OR r1 r2) F


--type MyG = XHaskell.RETypes.C ((S Z),(A,B)) (XHaskell.RETypes.C (Z,(A,A)) N)

--type LA = (LAB A)

--type LB = (LAB B)

--type LC = (LAB XHaskell.RENorm.C)

--foo :: (NIsToGr (XHaskell.RETypes.C (Z,(EMPT,EMPT)) N) (S Z) (OR EMPT PHI) (OR EMPT PHI) g) => g
--foo :: (IsToGr N Z (LA,(STAR LA)) (LA,(STAR LA)) g, GrToRe g Z g', Simplify g' g'') => g''
--foo :: (IsToGr N Z (OR LA LB) (OR LA LC) g, GrToRe g Z g') => g'
--foo :: (IsToGr N Z LA LA g, GrToRe g Z g') => g'
--foo :: (ISect (LA,(STAR LA)) ((STAR LA),LA) r) => r
--foo :: (ISect (STAR (OR LA LB)) ((STAR ((STAR LA),LB)),(STAR LA)) r) => r
--foo = Chameleon.Primitive.undefined



