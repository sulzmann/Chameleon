




class Erk a where erk::a
class Bar a where bar::a
class Foo a where foo::a

rule Erk a, Foo b ==> Bar b

f'  = (erk, let g :: (Foo a)=>a
                g = bar
            in g)
