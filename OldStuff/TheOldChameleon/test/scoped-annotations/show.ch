

class Show a where
  show :: a->String
  read :: String->a

data String = String

g :: Show a => String -> a -> (String,String)
g s x = (show (read s), show x)
