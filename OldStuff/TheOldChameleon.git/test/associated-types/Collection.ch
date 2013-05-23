data Bit    = One | Zero 
data BitSet = BS Bit BitSet | NIL

class CollectionFD c e | c -> e where
   emptyFD  :: c
   insertFD :: e -> c -> c
   toListFD :: c -> [e]

instance CollectionFD [a] a where
   emptyFD      = []
   insertFD b s = b:s
   toListFD b     = b

instance CollectionFD BitSet Bit where
   emptyFD       = NIL
   insertFD b bs = BS b bs
   toListFD (BS b bs) = b:(toListFD bs) 
   toListFD (NIL)     = []



class CollectionAT c where
   type Elem c
   emptyAT  :: c
   insertAT :: Elem c -> c -> c
   toListAT :: c -> [Elem c]

instance CollectionAT BitSet where
   Elem BitSet = Bit
   emptyAT       = NIL
   insertAT b bs = BS b bs
   toListAT (BS b bs) = b:(toListAT bs) 
   toListAT (NIL)     = []

instance CollectionAT [a] where
   Elem [a]     = a
   emptyAT      = []
   insertAT b s = b:s
   toListAT b     = b

d1 = toListFD (BS One (BS Zero NIL))
d2 = toListAT (BS One (BS Zero NIL))
d3 = insertFD One (BS One (BS Zero NIL))
d4 = insertAT One (BS One (BS Zero NIL))
d5 = insertFD True []
d6 = insertAT True []
d7 = insertFD One
d8 = insertAT One
