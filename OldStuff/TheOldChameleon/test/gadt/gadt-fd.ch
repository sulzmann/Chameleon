
data Erk a = (a=Int) => I a
           | (a=Bool) => B a


undef = undef

one :: Int
one = undef

f :: Erk a -> a
f (I x) = (one::Int) -- f (I x) = one       (*)
f (B x) = True
