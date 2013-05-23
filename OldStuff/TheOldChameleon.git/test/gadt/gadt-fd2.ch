
-- recast of gadt-fd.ch example in terms of FDs


class I a | -> a
class B a | -> a

instance I Int
instance B Bool

data Erk a = (I a) => I a
           | (B a) => B a


undef = undef

one :: Int
one = undef

f :: Erk a -> a
f (I x) = (one::Int) 
--f (I x) = one         --(*)
f (B x) = True
