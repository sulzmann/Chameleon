zip2 :: [a] -> [b] -> [(a,b)]
zip2 = Chameleon.Primitive.undefined

class ZipFD a b c | c->a, c->b where
   zipFD :: [a] -> [b] -> c

instance ZipFD a b [(a,b)] where
   zipFD = zip2

instance ZipFD (a,b) c e => ZipFD a b ([c]->e) where
   zipFD a b c = zipFD (zip2 a b) c

class Eq a b
rule Eq a b <==> a=b

class ZipAT c where
   type F1 c
   type F2 c
   type Fst c
   type Snd c
   zipAT  :: [F1 c] -> [F2 c] -> c


instance ZipAT [(a,b)] where
   F1 [(a,b)] = a
   F2 [(a,b)] = b
   zipAT = zip2

instance (ZipAT e, Eq (F2 e) c) => ZipAT ([c]->e) where
   Fst (a,b) = a
   Snd (a,b) = b
   F1 ([c]->e) = (Fst (F1 e))
   F2 ([c]->e) = (Snd (F1 e))
   zipAT a b c = zipAT (zip2 a b) c

d1 x y z = zipFD x y (z::[Int])
d2 x y z = zipAT x y (z::[Int])

