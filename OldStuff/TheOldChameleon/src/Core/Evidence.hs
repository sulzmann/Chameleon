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
-- Implements the (dictionary-passing) evidence translation for type classes.
--
--------------------------------------------------------------------------------

module Core.Evidence (
    buildMatch, checkDemanded, checkGiven,
    translateProg
) where

import Data.List

import Core.Justify
import qualified AST.Internal as AST

--------------------------------------------------------------------------------

-- builds a match from two (matchable) justifications
buildMatch :: LocInfo -> (Just,Just) -> Maybe Match
buildMatch jinfo (d,g) =
     do d1 <- checkDemanded jinfo d
        g1 <- checkGiven jinfo g
        match (elem (head g1) (annotJust jinfo)) (superJust jinfo) d1 g1
         

-- check whether we need to build a match for this justification
checkDemanded :: LocInfo -> Just -> Maybe [Loc]
checkDemanded jinfo (J js'@(j:js)) = 
    if ((elem j (demandedJust jinfo)) && 
        -- leading justifcation must be demanded
        (and (map (\x->elem x (allinstJust jinfo)) js)))
        -- remaining justifications must belong to instances
      then Just js' 
      else Nothing


-- check whether justification can be used for construction
-- e.g. consider
-- rule Foo a ==> (Bar a)_1
-- f :: (Foo a)_2 => ...
-- In the given store we'll find (Foo a)_2 and (Bar a)_[2,1] but only 
-- (Foo a)_2 is useful
checkGiven :: LocInfo -> Just -> Maybe [Loc]
checkGiven jinfo (J js'@(j:js)) 
  | ((elem j (annotJust jinfo)) &&   -- leading justification must come 
                                     -- from an annotation or pattern
     (and (map (\x->elem x (union (superJust jinfo)
                            (allinstJust jinfo))) js)))
                                     -- remaining justifications must belong to 
                                     -- some instance or superclass
                                  =  Just js' 
  | (elem j (patternJust jinfo)) = 
	    if (and (map (\x->elem x (union (superJust jinfo)
					(allinstJust jinfo))) (tail js)))
            -- RECALL: by construction  js' must be of the form (j:j'':js'')
            -- pattern case!
              then Just js'
              else Nothing
  | otherwise = Nothing

----------------------------------------

-- check whether a matching exists,
-- if yes compute the resulting match
-- Assumption: 
-- (1) Justifications with a leading
-- function location have already been preprocessed.
-- (2) Demanded justifications do not contain extractors 
-- the bool flag indicates the annotation (True) or pattern (False) case
match :: Bool -> Locs -> Locs -> Locs -> Maybe Match
match b extractors demanded given = 
  if b then -- annotation case
   let (j1:j1s) = given
       (j2:j2s) = demanded
   in do -- j3s are extractors, j4s are non-extractors
	 (j3s,j4s) <- transform j1s 
         j5s       <- split j2s j4s -- j2s = j5s ++ j4s
         return ([j2] ++ j5s ++ (reverse j3s) ++ [j1]) -- return the match
 else -- pattern case
   let (i1:i2:j1s) = given
       (j2:j2s) = demanded
   in do -- j3s are extractors, j4s are non-extractors
	 (j3s,j4s) <- transform j1s 
         j5s       <- split j2s j4s -- j2s = j5s ++ j4s
         return ([j2] ++ j5s ++ (reverse j3s) ++ [i2,i1]) -- return the match
 
 where
   -- transform js to (j1,j2) where 
   -- js = j1 ++ j2, and
   -- j1 contains only extractors, and
   -- j2 does not contain any extractors
   transform [] = Just ([],[])
   transform (j:js) 
     |  elem j extractors = do (j1,j2) <- transform js
                               return (j:j1,j2)
     |  otherwise         = do (j1,j2) <- transform js
                               if j1 == []
                                then return ([],(j:j2))
                                else fail "transformation not possible"  
   -- split j1 j2 = j3 s.t. j1 = j3 ++ j2
   -- note: reverse (j3 ++ j2) = (reverse j2) ++ (reverse j3)
   split j1 j2 = do j3 <- split2 (reverse j1) (reverse j2)
                    return (reverse j3)

   -- split2 j1 j2 = j3 s.t. j1 = j2 ++ j3
   split2 [] [] = Just []
   split2 (js@(j:j1)) [] = return js
   split2 (j:j1) (j':j2) 
        | j == j'   = do j3 <- split2 j1 j2
                         return (j:j3)
        | otherwise = fail "split not possible"
   split2 _ _  = fail "split not possible"

--------------------------------------------------------------------------------
-- evidence translation for an entire program (module), given a list of matches

translateProg :: LocInfo -> Matches -> AST.Prog -> AST.Prog
translateProg jinfo ms p = p

----------------------------------------

constructDictionary :: LocInfo -> Matches -> Maybe [AST.Exp]
constructDictionary jinfo jss = construct (constinstJust jinfo) jss

----------------------------------------
-- helper functions for building expressions

mkId :: String -> AST.Id
mkId str = AST.mkId srcinfo str

mkVar :: String -> AST.Exp
mkVar str = AST.VarExp (mkId str)

mkApp :: AST.Exp -> AST.Exp -> AST.Exp
mkApp e1 e2 = AST.AppExp srcinfo e1 e2

mkLet :: String -> AST.Exp -> AST.Exp -> AST.Exp
mkLet str e1 e2 = AST.LetExp srcinfo [lb] e2
  where
    lb = AST.LetBnd srcinfo (mkId str) e1

srcinfo = AST.evidenceTransSrcInfo

----------------------------------------
-- building names of evidence values (constructors, extractors)

--refers to a variable
dictionaryName :: Locs -> String
dictionaryName js = "d" ++ (buildName js)

dictionaryName' :: Locs->String
dictionaryName' js = "d'" ++ (buildName js)

dictionarySeparator :: String
dictionarySeparator = "X"

-- either (instance) constructor or (superclass) extractor
dictionaryConstructor :: Locs -> String
dictionaryConstructor js = "e" ++ (buildName js)

buildName :: Locs -> String
buildName [j] = show j
buildName (j:js) = (show j) ++ dictionarySeparator ++ (buildName js)


-- construct evidence out of a list of matches
-- cdc holds the list of constant dictionary constructors
construct :: Locs -> Matches -> Maybe [AST.Exp]
construct cdc jss = do jss2 <- collect (sort jss)
                       mapM (build cdc) jss2
             

    -- collect justifications with the same leading number
    -- collect jss = [js1, ..., jsn] where
    -- jsi = [(pi:jsi1),...,(pi:jsim)]
    -- Assumption: jss is sorted
collect :: Matches -> Maybe [Matches]
collect [] = return [] 
collect (js@(p':js'):jss') = do 
    (js1,jss1) <- separate p' jss'
    jss2       <- collect jss1
    return ([js:js1] ++ jss2)
    

    -- we consider a particular number
    -- separate p jss = (jss1,jss2) where
    -- js in jss1 all start with p and jss2 contains the rest
    -- Assumption: jss is sorted
separate :: Loc -> Matches -> Maybe (Matches,Matches)
separate p [] = return ([],[])
separate p (jss@(js@(p':js'):jss'))
        | p == p'   = do (js1,jss1) <- separate p jss'
                         return ([js] ++ js1, jss1)
        | otherwise = return ([],jss)


    -- build evidence for a particular location
build :: Locs -> Matches -> Maybe AST.Exp
-- Base case
build cdc [[i,j]]  
 | elem j cdc  -- j refers to a constant dictionary constructor
               = return (mkLet (dictionaryName' [i]) 
			(mkVar (dictionaryConstructor [j]))
                        (mkVar (dictionaryName' [i])))
                 -- let di = ej in di
 | otherwise   = return (mkLet (dictionaryName' [i]) 
			(mkVar (dictionaryName [j]))
                        (mkVar (dictionaryName' [i])))
                    -- let di = dj in di
-- Inductive case
build cdc jss =     
                let p = head (head jss)
                in do (k,jss') <- extract jss
                      exprs    <- construct cdc (sort jss')  -- dk1, ..., dks
                      exp      <- let f = (mkVar (dictionaryConstructor 
						    (sort (nub k))))
				  in  apply f exprs
                                      -- ek1...ks
                      return (mkLet (dictionaryName' [p]) exp
			     (mkVar (dictionaryName' [p])))
                      -- let dp = (...(ek1...ks dk1) ... dks) in dp

    -- extract [j1s,...,jns] = (k,[j1:j1s',...,jn:jns'] where
    -- k = [j1,...,jn]
    -- j1s = p:j1:j1s', ...,jns = p:jn:jns' 
extract :: Matches -> Maybe (Match,Matches)
extract [] = return ([],[])
extract (js:jss) =     do (k,jss') <- extract jss
                          return ((head (tail js)):k, [tail js]++jss') 

    -- apply a function to n arguments
apply e1 [] = return e1
apply e1 (e:es) = apply (mkApp e1 e) es

