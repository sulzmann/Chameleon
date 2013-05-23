
data Zero
data Succ x

rule Add l m n, Add l m n' ==> n=n'
rule Add Zero m n <==> m=n
rule Add (Succ l) m n <==> Add l m n', n=Succ n'

-- type indexed data type
-- we keep track of the length of the list
data List a n =  (n= Zero) => Nil 
            | forall m. Add (Succ Zero) m n => 
                        Cons a (List a m) 


append ::  Add l m n => 
           List a l -> List a m -> List a n
append (Cons x xs) ys = Cons x (append xs ys)
append Nil ys = ys
