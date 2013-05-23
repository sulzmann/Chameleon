
class Foo a where foo::a->Int
instance Foo Int -- (F)
class Bar a b

data Erk a = forall b. Bar a b => K1 (a,b)
           | forall b. Bar a b => K2 (a,b)

g (K1 (a,b)) = a
g (K2 (a,b)) = foo a
