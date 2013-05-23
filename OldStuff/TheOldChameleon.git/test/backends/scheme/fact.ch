
data Nat = Z
	 | S Nat

(+) Z     n = n
(+) (S m) n = S ((+) m n)

(*) m n = mul Z m
  where
    mul a Z	= a
    mul a (S m) = mul (a+n) m

one   = S Z
two   = S one
three = S two
four  = S three

fact Z     = one
fact (S n) = (S n) * fact n

fib Z     = one
fib (S Z) = one
fib (S (S n)) = fib (S n) + fib n


test1 = fact four
test2 = fib (four + four)

pmf = pmf
