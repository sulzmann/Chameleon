--------------------------------------------------------------------------------
--
-- Chameleon primitives.
--
-- This module ought to be implicitly imported into every other 
-- (including the Prelude.)
--
--------------------------------------------------------------------------------

module Chameleon.Primitive
where

--------------------------------------------------------------------------------
-- Overloaded == is necessary for matching pattern literals.

{-
class Eq a where
    (==), (/=) :: a -> a -> Bool

    (/=) x y = not (x == y)

infix 4 ==

instance Eq Int	    where (==) = primEqInt
instance Eq Integer where (==) = primEqInteger
instance Eq Float   where (==) = primEqFloat
instance Eq Double  where (==) = primEqDouble
instance Eq Char    where (==) = primEqChar
-}

{-
instance Eq a => Eq [a] where 
    (==) []     []     = True
    (==) (x:xs) (y:ys) = x == y && xs == ys
    (==) _      _      = False
-}

{-
primitive primEqInt	:: Int -> Int -> Bool
primitive primEqInteger :: Integer -> Integer -> Bool
primitive primEqFloat   :: Float -> Float -> Bool
primitive primEqDouble  :: Double -> Double -> Bool
primitive primEqChar    :: Char -> Char -> Bool
-}

----------------------------------------
-- Comparison functions.


{-
primitive primGTInt	  :: Int -> Int -> Bool
primitive primGTInteger   :: Integer -> Integer -> Bool
primitive primGTFloat	  :: Float -> Float -> Bool
primitive primGTDouble    :: Double -> Double -> Bool

primitive primGTEqInt	  :: Int -> Int -> Bool
primitive primGTEqInteger :: Integer -> Integer -> Bool
primitive primGTEqFloat	  :: Float -> Float -> Bool
primitive primGTEqDouble  :: Double -> Double -> Bool

primitive primLTInt	  :: Int -> Int -> Bool
primitive primLTInteger	  :: Integer -> Integer -> Bool
primitive primLTFloat	  :: Float -> Float -> Bool
primitive primLTDouble    :: Double -> Double -> Bool

primitive primLTEqInt	  :: Int -> Int -> Bool
primitive primLTEqInteger :: Integer -> Integer -> Bool
primitive primLTEqFloat	  :: Float -> Float -> Bool
primitive primLTEqDouble  :: Double -> Double -> Bool
-}

--------------------------------------------------------------------------------
-- Overloaded fromInteger and fromRational are required for pattern matching
-- against numeric literals.

{-
class Num a where
    fromInteger :: Integer -> a  

instance Num Int     where fromInteger = primIntegerToInt
instance Num Integer where fromInteger = id
instance Num Float   where fromInteger = primIntegerToFloat
instance Num Double  where fromInteger = primIntegerToDouble

class Fractional a where
    fromRational :: Rational -> a

-}

--------------------------------------------------------------------------------
-- Primitive numerical operations.

{-
primitive primIntegerToInt    :: Integer -> Int
primitive primIntegerToFloat  :: Integer -> Float
primitive primIntegerToDouble :: Integer -> Double

primitive primAddInt :: Int -> Int -> Int
primitive primSubInt :: Int -> Int -> Int
primitive primMulInt :: Int -> Int -> Int
primitive primDivInt :: Int -> Int -> Int
-}


--------------------------------------------------------------------------------
-- The run-time error function.

primitive primError :: [Char] -> a
primitive patternMatchFailed :: [Char] -> a

-- noSuchField, undefinedMethod, 
--    patternMatchFailed, uninitialisedField :: [Char] -> a
noSuchField	   = primError
undefinedMethod	   = primError
-- patternMatchFailed = primError
uninitialisedField = primError

--------------------------------------------------------------------------------
-- Functions the desugaring transformation implicitly depends upon.

{-
id :: a -> a
id x = x

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

not :: Bool -> Bool
not b = if b then False else True

(&&) :: Bool -> Bool -> Bool
(&&) a b = if a then b else False

infixr 3 &&

----------------------------------------

-- succInt :: Int -> Int
succInt x = x `primAddInt` 1

ltInt, gtInt :: Int -> Int -> Bool
ltInt = primLTInt
gtInt = primGTInt

enumFromToInt :: Int -> Int -> [Int]
enumFromToInt x y = enum x 
  where
    enum x | x `primLTEqInt` y = x : enum (succInt x)
	   | otherwise	       = []

enumFromThenToInt :: Int -> Int -> Int -> [Int]
enumFromThenToInt x y z = enum x
  where
    delta = y `primSubInt` x
    cond  | x `primLTInt` y = (`primGTInt` z)
	  | otherwise	    = (`primLTInt` z)

    enum x | cond x    = []
	   | otherwise = x : enum (x `primAddInt` delta)


--------------------------------------------------------------------------------
-- Miscellaneous

otherwise :: Bool 
otherwise = True

data Rational

undefined :: a 
undefined = primError "undefined"

yo :: [Char]
yo = "Yo!"
-}
