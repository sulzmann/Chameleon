

class Eval a b where eval::a->b

fst (x,y) = x


f :: Eval a (b,c) => a->b
f x = let g :: (b,c)
          g = eval x
      in fst g
