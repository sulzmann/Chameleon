



class HasEmpty a where isEmpty :: a->Bool
instance HasEmpty [a] 
instance HasEmpty (Maybe a) 
class Erk a
instance Erk m => HasEmpty (m a)
instance Erk []      
instance Erk Maybe  

undef = undef

bind :: Monad a => a b -> a c -> a c
bind = undef
return :: Monad a => b -> a b
return = undef


data Maybe a = Just a | Nothing

test :: (Monad m, HasEmpty (m (m a))) => m a -> Bool
test y = let f :: d->Bool
             f x = isEmpty (bind y (return x)) --(y >> return x)
         in f y
