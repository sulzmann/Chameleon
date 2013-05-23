

class Eq a where (==) :: a->a->Bool

instance Eq Bool

instance Eq a => Eq [a]

head (x:xs) = x


--g :: Eq b => [b] -> Bool                        -- (1)
g :: [a] -> Bool                        -- (1)
g ys =  let f::c->[a]->Bool             -- (2)
            f _ [] = True
            f z (x:xs) = (f z [xs]) {- &&  -- (3)
                         ([z]==ys)      -- (4) -}
        in f (head ys) ys
