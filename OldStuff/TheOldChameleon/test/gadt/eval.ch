
-- Here's a standard GAD example
-- A well-typed interpreter for simply-typed programs

-- bug: only works if we comment out (*), but this should work
-- JW: No, it can't work, as written. If you change it to: 
--	eval3 (Fun f) = let g x = eval3 (f (Lift x))
--			in  g
--     Then it works.
--     The attempt to print a type error, though, fails. Which is a bug.

data Exp3 a = (a=Int) => Zero | (a=Int)=> Succ (Exp3 Int) 
           | (a=Int) => Plus (Exp3 Int) (Exp3 Int)
           | forall b c. (a=b->c) => Fun (Exp3 b->Exp3 c) 
           | forall b. App (Exp3 (b->a)) (Exp3 b)
           | Lift a

plus :: Int->Int->Int
plus = undef

undef = undef

zero :: Int
zero = undef

one :: Int
one = undef

eval3 :: Exp3 a -> a
eval3 Zero = zero
eval3 (Succ n) = (eval3 n) `plus` one
eval3 (Plus e1 e2) = (eval3 e1) `plus` (eval3 e2)
--eval3 (Fun f) = let f x = eval3 (f (Lift x))          (*)
--                in f
eval3 (App f e) = (eval3 f) (eval3 e)
eval3 (Lift x) = x

