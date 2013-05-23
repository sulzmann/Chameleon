

map f [] = []
map f (x:xs) = (f x):(map f xs)

undefined = undefined

prefix :: b->[[b]]->[[b]]
prefix x yss =
        let xcons :: c -> [b]->[b]
            xcons v ys = x:ys 
        in map (xcons undefined) yss