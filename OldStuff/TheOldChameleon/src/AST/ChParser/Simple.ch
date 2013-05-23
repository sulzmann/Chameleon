xmodule Main where

f :: ((A|B)*) -> (A*)
f (x :: ()) = x --(x,x,x)
f ((x :: A), (xs :: ((A|B)*))) = (x, (f xs))
f ((x :: B), (xs :: ((A|B)*))) = f xs

