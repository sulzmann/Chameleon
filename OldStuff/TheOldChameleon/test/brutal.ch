-- Without some sort of memoization we will continue to suck in benchmarks
-- like the following.

u = u

a = let b = (u,u,u,u,u,u)
        c = (b,b,b,b,b,b)
        d = (c,c,c,c,c,c)
        e = (d,d,d,d,d,d)
    in  e

