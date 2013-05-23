module XHaskell.RESubtype where

import XHaskell.RENorm
import XHaskell.RETypes

class RESubtype r1 r2 

instance RESubtype r r

-- magic rule to decompose larger components formed by determinization, like 
-- A*,A* ~ (A,(A*,A*|A*))|(), in which A*,A*|A* ~ will grow larger and break the coinduction.
{-
instance ( RESubtype r1 r
         , RESubtype r2 r
         ) => RESubtype (OR r1 r2) r
-}
-- but this doesn't work when the RHS is A*,A* again.
instance ( Norm r1 n1
         , Norm r2 n2
         , NRESubtype n1 n2 
         ) => RESubtype r1 r2 


class NRESubtype n1 n2 

instance NRESubtype PHI n 

instance ( NRESubtype n1 n2
         ) => NRESubtype (OR EMPT n1) (OR EMPT n2)


instance ( NRESubtype n1 n2
         , RESubtype r1 r2
         ) => NRESubtype (OR ((LAB l),r1) n1) (OR ((LAB l),r2) n2)

instance ( M2N m1 i1
         , M2N m2 i2
         , LeqT i2 i1 T
         , NRESubtype (OR m1 n1) n2
         ) => NRESubtype (OR m1 n1) (OR m2 n2)