module XHaskell.REtoHT where

import XHaskell.RETypes

data Or a b = L a | R b 
--           deriving Show

data Lab l = Lab l
--           deriving Show

data Phi = Phi 
--          deriving Show -- Phi should not have any value, but this is needed for instance Show [Phi]

class REtoHT r h | r -> h

instance REtoHT PHI Phi

instance REtoHT EMPT [Phi]

instance REtoHT (LAB l) (Lab l)

instance ( REtoHT r h
         , REtoHT r' h'
         ) => REtoHT (OR r r') (Or h h')

instance ( REtoHT r h
         ) => REtoHT (STAR r) [h] 

instance ( REtoHT r h
         , REtoHT r' h'
         ) => REtoHT (r,r') (h,h')

instance REtoHT N Phi

instance ( REtoHT m h
         , REtoHT ms hs
         ) => REtoHT (C m ms) (Or h hs)