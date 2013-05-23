data Nat = Z
	 | S Nat

one   = S Z
two   = S one
three = S two

data List a = Nil
	    | Cons a (List a)

append Nil	   ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

enum Z	   = Cons Z Nil
enum (S n) = Cons (S n) (enum n)

test = append (enum three) (enum two)
