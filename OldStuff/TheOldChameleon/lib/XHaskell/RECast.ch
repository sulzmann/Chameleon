module XHaskell.RECast where

import XHaskell.RESubtype
import XHaskell.REtoHT

data Maybe a = Just a | Nothing 

class DCast r1 r2 h1 h2 | r1 r2 -> h1 h2 where
    dcast :: r1 -> r2 -> h1 -> (Maybe h2)

instance ( RESubtype r2 r1
         , REtoHT r1 h1
         , REtoHT r2 h2
         ) => DCast r1 r2 h1 h2 where
    dcast = Chameleon.Primitive.undefined

class UCast r1 r2 h1 h2 | r1 r2 -> h1 h2 where
    ucast :: r1 -> r2 -> h1 -> h2

instance ( RESubtype r1 r2
         , REtoHT r1 h1
         , REtoHT r2 h2
         ) => UCast r1 r2 h1 h2 where
    ucast = Chameleon.Primitive.undefined