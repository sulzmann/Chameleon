
data KEY = forall a. Mk a (a->Int)

f (Mk x f) = f x

f1 (Mk x f) = let foo=x
              in f foo

-- the following variation yields an error, 
-- an existential variable escapes
--f2 (Mk x f) = let foo=x
--              in foo

class Key a where getKey::a->Int

data KEY2 = forall a. Key a => Mk2 a

g2 (Mk2 x) = getKey x

