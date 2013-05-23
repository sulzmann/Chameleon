--------------------------------------------------------------------------------
--
-- Copyright (C) 2004 The Chameleon Team
--
-- This program is free software; you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by the Free 
-- Software Foundation; either version 2 of the License, or (at your option) 
-- any later version. This program is distributed in the hope that it will be 
-- useful, but WITHOUT ANY WARRANTY; without even the implied warranty of 
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. 
-- See the GNU General Public License for more details. 
-- You should have received a copy of the GNU General Public License along
-- with this program; if not, write to the Free Software Foundation, Inc., 
-- 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
--
--------------------------------------------------------------------------------
--
-- Module for miscellaneous functions which don't fit elsewhere (but some of
-- which probably should.) None of these functions should require any other 
-- Chameleon module to be imported.
--
-- WARNING: The definition of isVarId assumes certain symbolic characters can 
--	    be part of a VarId. These are valid for Haskell, but would need to
--	    be modified should the source language change.
--
--------------------------------------------------------------------------------

module Misc.Utils (
    module Misc.Utils, trace
)
where

import IO
import Char
import System
import List
import Debug.Trace
import System.IO.Unsafe

import Misc.Defaults

--------------------------------------------------------------------------------

type Filename  = String
type UniqueNum = Int

type Row = Int
type Col = Int

--------------------------------------------------------------------------------

-- program identifiers and locations
type IdStr = String
type Loc   = Int

-- never part of an AST
noLoc = (-1) :: Loc 

--------------------------------------------------------------------------------

bug :: String -> a
bug str = exit ("BUG!: " ++ str)

warn :: String -> a -> a
warn str = trace ("BUG?: " ++ str)

--------------------------------------------------------------------------------

-- a class of monads that have a fresh number store (Ints)
class Monad m => HasNumSupply m where
    freshInt :: m Int

--------------------------------------------------------------------------------
-- multi-parameter type constructor ids

makeMultiTypeId :: Int -> String
makeMultiTypeId n = "{" ++ show n ++ "}"

isMultiTypeId :: String -> Bool
isMultiTypeId xs = 
    case xs of
	('{':xs) -> let (n,xs') = span isDigit xs
		    in  case xs' of
			    "}" -> True
			    _   -> False
	_ -> False

--------------------------------------------------------------------------------

-- all strings of (lower case) alphabetic characters 
-- (ordered by length, then alphabetically)
alphaStrings :: [String]
alphaStrings = map (:[]) alpha ++ [ as++[a] | as <- alphaStrings, a <- alpha ]
  where
    alpha = ['a'..'z']


----------------------------------------

-- removes the name qualifier from the front of the string
-- (also drops the final `.')
dropQual :: String -> String
dropQual xs@('.':_) = xs
dropQual xs = (reverse . takeWhile (/='.') . reverse) xs

-- returns the name qualifier from the front of the string 
-- (not including the final `.')
takeQual :: String -> String
takeQual ys = case dropWhile (/='.') (reverse ys) of
		"" -> ""
		('.':xs) -> reverse xs

----------------------------------------

showLines :: Show a => [a] -> String
showLines = unlines . map show

----------------------------------------

-- Tests if the two given lists are `similar' enough, returns Nothing if
-- they're not similar, otherwise Just n, where n is the similarity. A low n
-- indicates greater similarity than a high n.
-- Two strings are similar if:
--  - they're identical
--  - changing a single character in either (or both) makes them identical
-- Note: case is ignored, as is are module name qualifiers
similarStrings :: String -> String -> Maybe Int
similarStrings a0 b0 
    | a == b     = Just 0
    | max la lb <= 3 = Nothing
    | la == lb+1 = if any (==b) d1a then Just 1 else Nothing
    | lb == la+1 = if any (==a) d1b then Just 1 else Nothing
    | la == lb   = if or [ a == b | a <- d1a, b <- d1b ] then Just 2 
							 else Nothing
    | otherwise  = Nothing
  where
    a = tailMsg ("similarStrings, a0: " ++ a0) (dropQual (map toLower a0))
    b = tailMsg ("similarStrings, b0: " ++ b0) (dropQual (map toLower b0))
    la = length a0
    lb = length b0
    d1a = drop1 a
    d1b = drop1 b

    drop1 xs = drop1' [] xs []
    drop1' as []     _  = as
    drop1' as (x:xs) ys = drop1' ((reverse ys ++ xs) : as) xs (x:ys)

--------------------------------------------------------------------------------

-- functions for testing lists as sets

superset, subset, sameSet :: Eq a => [a] -> [a] -> Bool
subset   xs ys = all (`elem` ys) xs
sameset  xs ys = sameSet xs ys
sameSet  xs ys = subset xs ys && subset ys xs
superset xs ys = all (`elem`xs) ys


powerset :: [a] -> [[a]]
powerset []     = [[]]
powerset (x:xs) = let ps = powerset xs
		  in  ps ++ [ x : ys | ys <- ps ]

without :: Eq a => [a] -> [a] -> [a]
without xs ys = [ x | x <- xs, x `notElem` ys ]

-- true if first list is longer than second
longer :: [a] -> [a] -> Bool
longer (x:xs) (y:ys) = longer xs ys
longer []     _	     = False
longer _      []     = True

allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual (x:xs) = all (x==) xs

elimSupersets :: Eq a => [[a]] -> [[a]]
elimSupersets xss = 
    [ ys | (ys, yss) <- allLeft xss, not $ any (ys`superset`) yss ]

----------------------------------------

-- like `elem', but stops looking as soon as a greater element is found 
-- (so list should be sorted)
elemOrd :: Ord a => a -> [a] -> Bool
elemOrd x [] = False
elemOrd x (y:ys) | x == y = True
		 | x <  y = False
		 | otherwise = elemOrd x ys

----------------------------------------

-- True if the second list is a prefix of the first
hasPrefix :: Eq a => [a] -> [a] -> Bool
xs     `hasPrefix` []     = True
[]     `hasPrefix` ys     = False
(x:xs) `hasPrefix` (y:ys) = x == y && xs `hasPrefix` ys

xs `hasSuffix` ys = reverse xs `hasPrefix` reverse ys


-- true if the two lists share a non-empty common prefix
isCommonPrefix :: Eq a => [a] -> [a] -> Bool
isCommonPrefix (x:_) (y:_) | x == y = True
isCommonPrefix _ _ = False
 
-- returns the longest common prefix of the two lists
commonPrefix :: Eq a => [a] -> [a] -> [a]
commonPrefix (x:xs) (y:ys) | x == y = x : commonPrefix xs ys
commonPrefix _ _ = []

-- returns the longest common prefix of all the lists given
commonPrefixLists :: Eq a => [[a]] -> [a]
commonPrefixLists []  = []
commonPrefixLists xss = foldl1 commonPrefix xss

-- finds a common prefix of all the lists, then drops it from all of them
dropCommonPrefixLists :: Eq a => [[a]] -> [[a]]
dropCommonPrefixLists xss = let l = length (commonPrefixLists xss)
			    in  map (drop l) xss

-- first list appears in second
isSublist :: Eq a => [a] -> [a] -> Bool
isSublist xs ys = any (uncurry eq) (zip (repeat xs) (tls ys))
    where 
	tls []	       = []
	tls xxs@(_:xs) = xxs : tls xs
    
	eq []	    _  = True
	eq _	    [] = False
	eq (x:xs) (y:ys) | x == y    = eq xs ys
			 | otherwise = False

----------------------------------------

fst3 (a,_,_) = a
snd3 (_,b,_) = b
thd3 (_,_,c) = c

order2 ab@(a,b) | a <= b    = ab
		| otherwise = (b,a) 


----------------------------------------

-- iteratively applies f to x while condition p holds
whileM :: Monad m => (a -> Bool) -> (a -> m a) -> a -> m a
whileM p f x | p x	 = f x >>= whileM p f
	     | otherwise = return x

replicateM :: Monad m => Int -> m a -> m [a]
replicateM n c = mapM (const c) [1..n]

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM c [] = return False
anyM c (x:xs) = do
    b <- c x 
    if b then return b
	 else anyM c xs

return2 :: (Monad m, Monad n) => a -> m (n a)
return2 = return . return

----------------------------------------

-- threads a value e through a sequence of applications of some action f
thread :: Monad m => (e -> a -> m (e,b)) -> e -> [a] -> m (e,[b])
thread f e as = do (e', rs) <- proc e as []
                   return (e', reverse rs)
  where
    proc e []     rs = return (e,rs)
    proc e (a:as) rs = do (e',r) <- f e a
                          proc e' as (r:rs)

----------------------------------------

lookupBy :: (a -> b -> Bool) -> a -> [(b,c)] -> Maybe c
lookupBy eq a [] = Nothing
lookupBy eq a ((b,c):bcs) | a `eq` b  = Just c
			  | otherwise = lookupBy eq a bcs

----------------------------------------

minBy, maxBy :: (a -> a -> Ordering) -> a -> a -> a
minBy p a b = case p a b of LT -> a ; _ -> b
maxBy p a b = case p a b of GT -> a ; _ -> b

----------------------------------------

-- partitions xs into elements which satisfy p and those which don't. Also,
-- applies g to x in either case
partitionF :: (a -> Bool) -> (a -> a) -> [a] -> ([a], [a])
partitionF p g [] = ([], [])
partitionF p g (x:xs) = let (t, f) = partitionF p g xs
			    x' = g x
		        in  if p x then (x':t, f)
				   else (t, x':f)

-- pads out a string to length n by adding spaces to its end
pad n str = let len = length str
	    in  if len < n
		   then str ++ replicate (n - len) ' '
		   else str

-- pads first string to the length of the second by adding spaces to the end
-- first string is just returned if its already longer
padTo :: String -> String -> String
padTo (c:cs) (_:ks) = c : padTo cs ks
padTo cs@[]  (_:ks) = ' ' : padTo cs ks
padTo cs     []	    = cs


-- As below, but specialised for 80 columns
split80 :: String -> [String]
split80 = splitLine 65

-- Splits a long line, at whitespace, into segments no longer than specified.
-- It will try to avoid whitespace at the beginning of any line.
-- NOTE: If there's no whitespace before the limit, the line will over flow.
splitLine :: Int -> String -> [String]
splitLine len str = rep segments
  where
    rep :: [(Int, String)] -> [String]
    rep []  = []
    rep pss = let (s, rest) = take pss
		  rest' = [ (n - len, s) | (n,s) <- rest ]
	      in  s : rep rest'
  
    take :: [(Int, String)] -> (String, [(Int, String)])
    take [] = ([], [])
    take rest@((p1,s1):(p2,(s:s2)):pss)
	| isSpace s && p2 >= len = ([], rest)
    take rest@((p,s):pss) 
	| p >= len  = ([], rest)
	| otherwise = let (ss, rest) = take pss
		      in  (s++ss, rest)
  
    notSpace = not . isSpace

    segments :: [(Int, String)]
    segments = seg 0 (break str)
      where
	seg _ []     = []
	seg p (s:ss) = (p,s) : seg (p+length s) ss

    break []  = []
    break str = let (str1,str2) = span isSpace  str
		    (str3,str4) = span notSpace str2
		in  str1 : str3 : break str4
    



splitEither :: [Either a b] -> ([a], [b])
splitEither [] = ([], [])
splitEither ((Left l):es)  = let (ls, rs) = splitEither es in (l:ls, rs)
splitEither ((Right r):es) = let (ls, rs) = splitEither es in (ls, r:rs)
 
isLeft (Left _) = True
isLeft _ = False
isRight  = not . isLeft

fromLeft  (Left x)  = x
fromRight (Right x) = x

 
singleton [x] = True
singleton _   = False

notNull [] = False
notNull _  = True

-- inserts element into list at given position (starting from 0), anything
-- already at that position and following, is moved down
-- returns original list if position doesn't exist
insertAt :: Int -> a -> [a] -> [a] 
insertAt 0 x ys = x:ys
insertAt n x [] = []
insertAt n x (y:ys) = y : insertAt (n-1) x ys


conId, varId :: String -> String
conId "" = ""
conId (c:cs) = toUpper c : cs

varId "" = ""
varId (c:cs) = toLower c : cs

isVarId :: String -> Bool
isVarId cs0 = case cs of
		    ""	  -> False
		    (c:_) -> isLower c || c == '_' || all (`elem`syms) cs
  where
    cs   = dropQual cs0
    syms = ":!#$%&*+./<=>?@\\^|-~"


plural :: [a] -> String -> String
plural [x] str = str
plural _   str = str ++ "s"


showlist :: Show a => [a] -> String
showlist xs = unlines (map show xs)

showlists :: Show a => [a] -> String
showlists = concat . intersperse "\n\n" . map show

predIdStr cs = not (null cs) && isUpper (head cs)


permute [] = [[]] 
permute (x:xs) = [ take i ys ++ [x] ++ drop i ys 
                       | ys <- permute xs, i <- [0..length ys] ] 


-- given a list, returns a list of pairs where for all elements in the list,
-- each pair contains a list element along with all the *other* elements
allLeft xs = allLeft' xs []
    where allLeft' []     _  = []
          allLeft' (x:xs) as = (x, as ++ xs) : allLeft' xs (x:as)

leftOvers = allLeft
	      
-- returns a list which contains elements which appear in all of the input
-- lists
commonElems :: Eq a => [[a]] -> [a]
commonElems []	     = []
commonElems [xs]     = xs
commonElems (xs:xss) = foldl intersect xs xss
	  

intersection []	_ = []
intersection (x:xs) ys
  | x `elem` ys = x : intersection xs ys
  | otherwise	= intersection xs ys 
	  

-- reports message in the event of failure
headMsg msg [] = bug ("headMsg: " ++ msg)
headMsg _   xs = head xs

tailMsg msg [] = bug ("tailMsg: " ++ msg)
tailMsg _   xs = tail xs

initMsg msg [] = bug ("initMsg: " ++ msg)
initMsg _   xs = init xs

filler str = bug ("don't look at the: " ++ str)

-- finds elements of list which occur more than once
multiples :: Eq a => [a] -> [a]
multiples xs = nub $ mults xs
    where mults [] = []
	  mults (x:xs) | x `elem` xs = x : mults xs
		       | otherwise   = mults xs

-- returns string suffix following the last '/'
basename :: String -> String
basename str = reverse (takeWhile (/='/') (reverse str)) 

-- returns the remainder following the last '.' in the String (else "")
nameSuffix :: String -> String
nameSuffix str = let strs = tail (iterate suffix str)
		 in  skip strs
  where
    skip (xs:[]:_)  = xs
    skip (xs:ys:zs) = skip (ys:zs)
  
    suffix xs = let xs' = dropWhile (/='.') xs
		in  case xs' of
		     ('.':ys) -> ys
		     []	      -> []

-- returns everything before the last '.' in the filename
dropSuffix :: String -> String
dropSuffix str | '.' `notElem` str = str
	       | otherwise = let str' = dropWhile (/='.') (reverse str)
			     in  reverse (tail str')

addChSuffix :: String -> String
addChSuffix = (++ defaultFilenameExtension)

addSchemeSuffix :: String -> String
addSchemeSuffix = (++ schemeFilenameExtension)

chToSchemeSuffix :: String -> String
chToSchemeSuffix = addSchemeSuffix . dropSuffix

addLvmSuffix :: String -> String
addLvmSuffix = (++ lvmFilenameExtension)

chToLvmSuffix :: String -> String
chToLvmSuffix = addLvmSuffix . dropSuffix

-- change nth list element (from 1)
changeN :: Int -> [a] -> a -> [a]
changeN 1 (x:xs) y = y : xs
changeN n (x:xs) y = x : changeN (n-1) xs y
changeN _ [] _ = error "changeN"

-- returns nth element of list (from 1, unlike !!)
nthElem :: Int -> [a] -> a
nthElem 1 (x:xs) = x
nthElem n (x:xs) = nthElem (n-1) xs
nthElem _ []     = error "nthElem"


-- if condition is True, then return third arg., else bail out with message
assert :: Bool -> String -> a -> a
assert True  _   a = a
assert False msg a = unsafePerformIO $ do putStrLn ("ASSERT FAILED: " ++ msg)
					  exitFailure

-- terminates program returning a failed exit code
-- (just like `error', but only the given string is printed)
exit :: String -> a
exit str = unsafePerformIO (putStrLn str >> exitFailure)

-- as above, but exits successfully
exitOkay :: String -> a
exitOkay str = unsafePerformIO (putStrLn str >> exitSuccess)

exitSuccess :: IO a
exitSuccess = exitWith ExitSuccess

-- indent second string, and place first, as a title, to the left of its first
-- line
titleLeft :: String -> String -> String
titleLeft hdg str = let ls = lines str
			w  = length hdg
			ls'= indentRest w ls
		    in  unlines ls'
			
    where indentRest w [] = []
	  indentRest w (l:ls) = (hdg ++ l) : map (indent w) ls

	  indent w l = replicate w ' ' ++ l

--------------------------------------------------------------------------------

(|||) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
p ||| q = \x -> p x || q x

(&&&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
p &&& q = \x -> p x && q x

--------------------------------------------------------------------------------
-- error monad (just like Maybe, but can carry around error information)

data E a = Succ a 
	 | Err String 
    deriving Show

instance Monad E where
  m >>= k = case m of
		Succ a -> k a
		Err s -> Err s
  return x = Succ x
  fail s = Err s

isSucc, isErr :: E a -> Bool
isSucc (Succ _) = True
isSucc _        = False
isErr (Err _) = True
isErr _       = False

fromSucc :: E a -> a
fromSucc (Succ s) = s
fromSucc _	= error "fromSucc: not a Succ"

fromErr :: E a -> String
fromErr  (Err e)  = e
fromErr  _        = error "fromErr: not an Err"

fromSucc' s (Succ x) = x
fromSucc' s _ = error ("fromSucc: not a succ: " ++ s)

success = Succ (error "success!")

fromSuccFatalErr :: E a -> a
fromSuccFatalErr (Err msg) = exit msg
fromSuccFatalErr (Succ s ) = s

--------------------------------------------------------------------------------

-- combines monadic list results
(++>) :: Monad m => m [a] -> m [a] -> m [a]
(++>) xs ys = do xs' <- xs
                 ys' <- ys
                 return (xs' ++ ys')
                                  
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = mapM f xs >>= \xss -> return (concat xss)

--------------------------------------------------------------------------------

-- identity monad 

data Identity a = Identity { runIdentity :: a }

instance Monad Identity where
    return v = Identity v
    (Identity a) >>= f = f a

--------------------------------------------------------------------------------
isInfixId ""	= False
isInfixId (c:_) = not ((isAlphaNum c) || (isSpace c) || c == '(' || c == ')')

infixParens id  = if isInfixId id
                  then ("(" ++ id ++ ")")
		  else id

--------------------------------------------------------------------------------

fj str (Just x) = x
fj str Nothing  = bug ("fromJust: " ++ str)

fromJustMsg = fj

--------------------------------------------------------------------------------

-- a hack, but good enough
fileExists :: String -> IO Bool
fileExists fn = do r <- try (openFile fn ReadMode)
		   case r of
		    Left err -> return False
		    Right  h -> hClose h >> return True

-- as above, but also tries variants of filename ending in '.ch' and '.hs'
-- (if the name doesn't already have one of those suffixes)
-- Returns Nothing if the file doesn't exist, else Just the name of the file
-- that actually does exist (with any additional suffix added.)
chFileExists :: String -> IO (Maybe String)
chFileExists fn = do
    e <- fileExists fn
    let suf = nameSuffix fn
	fn_ch = fn ++ ".ch"
	fn_hs = fn ++ ".hs"
    if suf == "ch" || suf == "hs"
      then return (if e then Just fn else Nothing)
      else do
	ech <- fileExists fn_ch
	if ech then return (Just fn_ch)
	       else do ehs <- fileExists (fn_hs)
		       if ehs then return (Just fn_hs)
			      else return Nothing
