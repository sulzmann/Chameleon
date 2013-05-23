



class Foo a b where foo :: a->b->Int
instance Foo Int b 
instance Foo Bool b

plus :: Int->Int->Int
plus x y = 1

p y = (let  f :: c -> Int
            f x = foo y x 
       in f, y `plus` (1::Int))
 
q y = (y `plus` (1::Int), let f :: c -> Int
                              f x = foo y x 
                          in f) 