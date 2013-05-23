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
-- This module defines a number of built-in types and values, which are a core
-- part of the language.
--
--------------------------------------------------------------------------------

module Core.BuiltIn 

where

import qualified AST.Internal as AST
import Misc
import AST.SrcInfo
import Core.Name
import Core.Types
import Core.CHR
import Core.Constraint
import Core.Justify (noJust)

--------------------------------------------------------------------------------

-- tupleConStr builds the constructor name for n-tuples.
-- NOTE: the 1-tuple constructor should obviously never be used!

-- string names of built-in constructors
arrowStr   = "->"
consStr	   = ":"
listStr    = "[]"
nListStr n = if n == 0 then "[]" else "[]_" ++ show n
tupleStr n = ("(" ++ replicate (n-1) ',' ++ ")")
trueStr    = "True"
falseStr   = "False"
vnilStr	   = "<>"
vconsStr   = ";"
intStr	   = "Int"
integerStr = "Integer"
doubleStr  = "Double"
floatStr   = "Float"
ratioStr   = "Ratio"
stringStr  = "String"
charStr	   = "Char"
boolStr    = "Bool"
unitStr	   = "()"
starStr    = "*"
barStr     = "|"
phiStr     = "{}"

-- built-in functions
mSeqStr		  = ">>"
mBindStr	  = ">>="
negateStr	  = "negate"
concatMapStr	  = "Chameleon.Primitive.concatMap"
enumFromStr	  = "Chameleon.Primitive.enumFrom"
enumFromThenStr	  = "Chameleon.Primitive.enumFromThen"
enumFromToStr	  = "Chameleon.Primitive.enumFromTo"
enumFromThenToStr = "Chameleon.Primitive.enumFromThenTo"
fromIntegerStr	  = "Chameleon.Primitive.fromInteger"
fromRationalStr   = "Chameleon.Primitive.fromRational"
mkRatioStr	  = "Ratio.%"
noSuchFieldStr	      = "Chameleon.Primitive.noSuchField"
undefinedMethodStr    = "Chameleon.Primitive.undefinedMethod"
uninitialisedFieldStr = "Chameleon.Primitive.uninitialisedField"
patternMatchFailedStr = "Chameleon.Primitive.patternMatchFailed"

-- Built-in versions of Prelude functions we depend on, defined independently 
-- of the Prelude (in Chameleon.Primitive)
bAndStr		 = "Chameleon.Primitive.&&"	 -- and
bEqualsStr	 = "Chameleon.Primitive.=="	 -- (==)
bMapStr		 = "Chameleon.Primitive.map"	 -- map
bAppendStr	 = "Chameleon.Primitive.++"	 -- append (++)
bSuccIntStr	 = "Chameleon.Primitive.succInt" -- successor on Ints
bLTIntStr	 = "Chameleon.Primitive.ltInt"	 -- less-than (<) on Ints
bGTIntStr	 = "Chameleon.Primitive.gtInt"   -- greater-than (>) on Ints
bEnumFromToIntStr     = "Chameleon.Primitive.enumFromToInt"-- enumFromTo on Ints
bEnumFromThenToIntStr = "Chameleon.Primitive.enumFromThenToInt"	-- enumFromThenTo on Ints


-- built-in patterns
dontcareStr = "_"

-- built-in type classes
numStr	      = "Prelude.Num"
fractionalStr = "Prelude.Fractional"

--------------------------------------------------------------------------------
-- type, pattern and expression AST constructors


----------------------------------------
-- type constructors

tupleTypeCon :: SrcInfo -> Int -> AST.Type
tupleTypeCon s n = AST.ConType (AST.mkId s (tupleStr n))

arrowTypeCon :: SrcInfo -> AST.Type
arrowTypeCon s = AST.ConType (AST.mkId s arrowStr)

listTypeCon :: SrcInfo -> AST.Type
listTypeCon s = AST.ConType (AST.mkId s listStr)

starTypeCon :: SrcInfo -> AST.Type
starTypeCon s = AST.ConType (AST.mkId s starStr)

unionTypeCon :: SrcInfo -> AST.Type
unionTypeCon s = AST.ConType (AST.mkId s barStr)

empTypeCon :: SrcInfo -> AST.Type
empTypeCon s = AST.ConType (AST.mkId s unitStr)

phiTypeCon :: SrcInfo -> AST.Type
phiTypeCon s = AST.ConType (AST.mkId s phiStr)

----------------------------------------
-- pattern constructors

truePatCon :: SrcInfo -> AST.Pat
truePatCon s = AST.ConPat s (AST.mkId s trueStr) []

falsePatCon :: SrcInfo -> AST.Pat
falsePatCon s = AST.ConPat s (AST.mkId s falseStr) []

----------------------------------------
-- expression constructors

tupleExpCon :: SrcInfo -> Int -> AST.Exp
tupleExpCon s n = AST.ConExp (AST.mkId s (tupleStr n))

nListExpCon :: SrcInfo -> Int -> AST.Exp
nListExpCon s n = AST.ConExp (AST.mkId s (nListStr n))

{-
listExpCon :: SrcInfo -> AST.Exp
listExpCon s = AST.ConExp (AST.Id s listStr)
-}

--------------------------------------------------------------------------------
-- built-in types

tupleType :: [Type] -> Type
tupleType [t] = t
tupleType ts = let con = TCon $ mkFreeName $ tupleStr (length ts)
	       in  foldl TApp con ts

tupleConType :: Int -> Type
tupleConType n =     
    let vs   = map (TVar . mkVar) (take n alphaStrings) 
    in  foldr arrow (tupleType vs) vs

arrow :: Type -> Type -> Type
arrow t1 t2 = let arr = TCon (mkFreeName arrowStr)
	      in  TApp (TApp arr t1) t2

nListConType :: Int -> Type
nListConType n =
    let a = TVar (mkVar "a")
    in  foldr arrow (listType a) (replicate n a)

listType :: Type -> Type
listType = TApp (TCon (mkFreeName listStr))

ratioType :: Type -> Type
ratioType = TApp (TCon (mkFreeName ratioStr))

vnilType, vconsType :: Type
vnilType  = TCon (mkFreeName vnilStr)
vconsType = TCon (mkFreeName vconsStr)

charType, floatType, doubleType, rationalType, intType, integerType, 
	  boolType, stringType, unitType :: Type
charType     = TCon (mkFreeName charStr)
floatType    = TCon (mkFreeName floatStr)
doubleType   = TCon (mkFreeName doubleStr)
rationalType = ratioType integerType
intType	     = TCon (mkFreeName intStr)
integerType  = TCon (mkFreeName integerStr)
boolType     = TCon (mkFreeName boolStr)
unitType     = TCon (mkFreeName unitStr)
stringType   = listType charType

--------------------------------------------------------------------------------
-- built-in type classes (un-justified)

numCons t	 = UC (mkFreeName numStr) [t] noJust
fractionalCons t = UC (mkFreeName fractionalStr) [t] noJust

--------------------------------------------------------------------------------
-- built-in CHRs

builtInCHRs :: [CHR]
builtInCHRs = [ consCHR, 
		nilCHR,
		trueCHR,
		falseCHR,
		unitCHR ] ++
		-- noSuchFieldCHR,
		-- undefinedMethodCHR,
		-- uninitialisedFieldCHR,
		-- patternMatchFailedCHR,
		-- bAndCHR,
		-- bEqualsCHR,
		-- bMapCHR,
		-- bAppendCHR,
		-- bSucc_IntCHR,
		-- bLessThan_IntCHR,
		-- bGreaterThan_IntCHR,
		-- bEnumFromTo_IntCHR,
		-- bEnumFromThenTo_IntCHR] ++
	      map nListCHR [1..7] ++
	      map tupleCHR [2..7]


-- The function which reports when a field projection function is applied to a
-- constructor which doesn't contain that field.
noSuchFieldCHR = genericFailCHR noSuchFieldStr

-- Reports an error if we try to use an undefined method for some instance.
undefinedMethodCHR = genericFailCHR undefinedMethodStr

-- A placeholder for an uninitialised field in a record.
uninitialisedFieldCHR = genericFailCHR uninitialisedFieldStr

-- The function invoked in case we run out of alternative patterns in a match.
patternMatchFailedCHR = genericFailCHR patternMatchFailedStr

genericFailCHR :: String -> CHR
genericFailCHR str = 
    let uc   = njUC (mkFreeName str) [TVar (mkVar "t")]
	info = NoCHRInfo
    in  SimpRule info [uc] trueConstraint

-- NOTE: don't use this rule (it's wrong)
c0VarsCHR = 
    let uc t = njUC (mkFreeName "C0Vars!") [t]
	a = TVar (mkVar "a")
	b = TVar (mkVar "b")
	info = NoCHRInfo
    in  SimpRule info [uc a, uc b] (toConstraint (uc (tupleType [a,b])))

consCHR :: CHR
consCHR = 
    let t    = TVar (mkVar "t")
	a    = TVar (mkVar "a")
	uc   = njUC (mkFreeName consStr) [t]
	typ  = a `arrow` (listType a `arrow` listType a)
	info = NoCHRInfo 
    in  SimpRule info [uc] (toConstraint (t =:= typ))

nilCHR = 
    let t    = TVar (mkVar "t")
	a    = TVar (mkVar "a")
	uc   = njUC (mkFreeName listStr) [t]
	typ  = listType a
	info = NoCHRInfo 
    in  SimpRule info [uc] (toConstraint (t =:= typ))

trueCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName falseStr) [t]
	typ  = boolType
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))

falseCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName trueStr) [t]
	typ  = boolType
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))

unitCHR = 
    let	t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName unitStr) [t]
	typ  = unitType
	info = NoCHRInfo
    in	SimpRule info [uc] (toConstraint (t =:= typ))

nListCHR n = 
    let t    = TVar (mkVar "t")
	a    = TVar (mkVar "a")
	uc   = njUC (mkFreeName (nListStr n)) [t]
	typ  = foldr arrow (listType a) (replicate n a)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


tupleCHR n = 
    let t    = TVar (mkVar "t!")
	uc   = njUC (mkFreeName (tupleStr n)) [t]
	typ  = tupleConType n
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))

----------------------------------------
-- Built-in helper functions
-- These are invoked by automatically derived instances.


-- built-in and
bAndCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName bAndStr) [t]
	typ  = boolType `arrow` (boolType `arrow` boolType)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


-- built-in (==)
bEqualsCHR = 
    let t    = TVar (mkVar "t")
	a    = TVar (mkVar "a")
	uc   = njUC (mkFreeName bEqualsStr) [t]
	typ  = a `arrow` (a `arrow` boolType)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


-- built-in map
bMapCHR = 
    let t    = TVar (mkVar "t")
	a    = TVar (mkVar "a")
	b    = TVar (mkVar "b")
	uc   = njUC (mkFreeName bMapStr) [t]
	typ  = (a `arrow` b) `arrow` (listType a `arrow` listType b)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


-- built-in append (++)
bAppendCHR = 
    let t    = TVar (mkVar "t")
	a    = TVar (mkVar "a")
	uc   = njUC (mkFreeName bAppendStr) [t]
	typ  = listType a `arrow` (listType a `arrow` listType a)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))

{-
-- built-in successor on Ints
bSucc_IntCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName bSucc_IntStr) [t]
	typ  = intType `arrow` intType 
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))

-- built-in less-than (<) on Ints
bLessThan_IntCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName bLessThan_IntStr) [t]
	typ  = intType `arrow` (intType `arrow` boolType)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


-- built-in greater-than (>) on Ints
bGreaterThan_IntCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName bGreaterThan_IntStr) [t]
	typ  = intType `arrow` (intType `arrow` boolType)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


-- enumFromTo in Ints
bEnumFromTo_IntCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName bEnumFromTo_IntStr) [t]
	typ  = intType `arrow` (intType `arrow` listType intType)
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))


-- enumFromThenTo in Ints
bEnumFromThenTo_IntCHR = 
    let t    = TVar (mkVar "t")
	uc   = njUC (mkFreeName bEnumFromThenTo_IntStr) [t]
	typ  = intType `arrow` (intType `arrow` (intType `arrow` 
						 listType intType))
	info = NoCHRInfo
    in  SimpRule info [uc] (toConstraint (t =:= typ))

-}
