class ArithmeticFD a b c | a b -> c where
   plusFD :: a -> b -> c

instance ArithmeticFD Int Int Int where
   plusFD = Chameleon.Primitive.undefined

instance ArithmeticFD a b c => ArithmeticFD [a] [b] [c] where
   plusFD (a:x) (b:y) (c:z) = (plusFD a b c):(plusFD x y z)
   plusFD [] [] []             = []


class ArithmeticAT a b where
   type Result a b
   plusAT :: a -> b -> Result a b

instance ArithmeticAT Int Int where
   Result Int Int = Int
   plusAT = Chameleon.Primitive.undefined

instance ArithmeticAT a b => ArithmeticAT [a] [b] where
   Result [a] [b] = [Result a b]
   plusAT = Chameleon.Primitive.undefined
   plusAT (a:x) (b:y) (c:z) = (plusAT a b c):(plusAT x y z)
   plusAT [] [] []             = []
   
d1 a b = plusFD (a::[Int]) (b::[Int])
d2 a b = plusAT (a::[Int]) (b::[Int])
d3 a = plusFD (a::[Int])
d4 a = plusAT (a::[Int])
