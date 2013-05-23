module XHaskell.REInference where

import XHaskell.RENorm
import XHaskell.REOpts
import XHaskell.RETypes

data VARPat r
data PAIRPat p1 p2

class Infer t pats result | t pats -> result


instance Infer PHI N (N,N)

instance ( StripT p pa
         , ISect r pa rp
         , Diff r rp r'
         , InferOne rp p rg
         , Infer r' ps (rps,rgs)
         ) => Infer r (XHaskell.RETypes.C p ps) ((XHaskell.RETypes.C rp rps),(XHaskell.RETypes.C rg rgs))


class StripT p pa | p -> pa

instance StripT (VARPat r) r

instance ( StripT p1 r1
         , StripT p2 r2
         ) => StripT (PAIRPat p1 p2) (r1,r2)


class InferOne rp p rg | rp p -> rg

instance ( StripT p1 ra1
         , StripT p2 ra2
         , LBreak rp ra1 ra2 rp1
         , RBreak rp ra1 ra2 rp2
         , InferOne rp1 p1 rg1
         , InferOne rp1 p2 rg2
         ) => InferOne rp (PAIRPat p1 p2) (rg1,rg2)

instance ( ISect rp r rg
         ) => InferOne rp (VARPat r) rg


class REEQ r1 r2 | r1 -> r2, r2 -> r1

instance REEQ r r 