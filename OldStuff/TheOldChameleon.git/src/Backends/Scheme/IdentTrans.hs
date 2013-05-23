module Backends.Scheme.IdentTrans (f) where

import Char (ord, isAscii, isLower)
import List (concatMap, (\\))
import Numeric (showHex)

import Backends.Scheme.AST

import AST.Common

f :: Id -> SId
f id =
  let str = idStr id in
  SId ('h' : concatMap trChar str)

-- | translate a single character of a Haskell identifier into a string suitable
-- for a Scheme identifier. Differences:
-- 
-- 1. Scheme is case-insensitive
-- 2. Scheme does not allow all of Haskell's symbol characters inside
-- identifiers 
-- 3. Resolved Haskell symbols may contain parentheses (which are illegal in
-- Schem identifiers)
-- 
-- Hence, we map each character which is neither a <special initial> nor a
-- lowercase letter to its unicode escape %uHHHH
trChar :: Char -> String
trChar ch =
  let unicoded = '%':'u': hexn 4 (ord ch) in
  if isAscii ch && (isLower ch || ch `elem` preservedCharacters)
  then [ch]
  else unicoded

-- | last n digits of the hex representation of an integer
hexn :: Int -> Int -> String
hexn n i = reverse $ take n $ (reverse (showHex i "") ++ repeat '0')

-- | cf R5RS <special initial>
specialInitial :: String
specialInitial = "!$%&*/:<=>?^_~"
-- | cf R5RS <special subsequent>
specialSubsequent :: String
specialSubsequent = "+-.@"

-- | need to exclude % but include <special subsequent>
preservedCharacters :: String
preservedCharacters = specialSubsequent ++ (specialInitial \\ "%")
