module XHaskell.RETypes where

data EMPT = EMPT
--            deriving Show
data STAR r = STAR r
--              deriving Show
data OR r r' = OR r r'
--               deriving Show
data LAB l = LAB l
--           deriving Show
data PHI = PHI
--           deriving Show


--some aux datatypes

data T = T
data F = F

data N = N
data C x xs = C x xs

data Z = Z
data S n = S n


