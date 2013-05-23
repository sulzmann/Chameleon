

undefined = undefined

class Foo a
class Foo2 a

data  Bar a = Foo a => Bar a
            | Foo2 a => Bar2 a
             
--f :: Bar a -> Bool
f (Bar x) = True
f (Bar2 x) = True