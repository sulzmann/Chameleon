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
-- | Tokens for the Chameleon parser.
--
--------------------------------------------------------------------------------

module AST.ChParser.Tokens 
where

import qualified AST.Token as AST

--------------------------------------------------------------------------------
-- simple position information

-- module name, row and column of source
type SrcPos = (String, Int, Int)

-- | Refers to no specific source position. (Note though that this is not a
-- unique reference. All of these `noSrcPos' things are equivalent.)
noSrcPos :: SrcPos
noSrcPos = AST.noSrcPos

-- | Something paired with a source position.
type Src a = (a, SrcPos)

-- | Formats a `SrcPos' as a fairly verbose string.
formatSrcPosVerbose :: SrcPos -> String
formatSrcPosVerbose (mod, x, y) = "line " ++ show x ++ ", col. " ++ show y

----------------------------------------

-- | Creates a token without any `Src'. (Actually it's _|_.)
mkNoSrc :: (Src a -> Token) -> Token
mkNoSrc tk = tk (error "AST.ChParser.Tokens: token has an undefined Src field")

-- | Gets the value (non-source info.) part of a `Src' pairing.
srcVal :: Src a -> a
srcVal = fst

-- | Source tokens.
data Token  = TId	    (Src String)	    -- ^ variable id
	    | TConId	    (Src String)	    -- ^ constructor id.
	    | TIId	    (Src String)	    -- ^ infix id.
	    | TInt	    (Src (Integer,String))  -- ^ int lit.
	    | TFloat	    (Src (Double,String,(Integer,Integer))) 
						    -- ^ float lit.
	    | TChar	    (Src Char)		    -- ^ char. lit.
	    | TStr	    (Src String)	    -- ^ string lit.
	    | TMinus	    (Src String)	    -- ^ `-' (minus sign\\dash)
	    | TRule         (Src String)	    -- ^ rule 
	    | TOverload     (Src String)	    -- ^ overload 
	    | TClass	    (Src String)	    -- ^ class 
	    | TInstance     (Src String)	    -- ^ instance 
	    | TDeriving	    (Src String)	    -- ^ deriving 
	    | TInfix	    (Src String)	    -- ^ infix 
	    | TInfixl	    (Src String)	    -- ^ infixl 
	    | TInfixr	    (Src String)	    -- ^ infixr 
	    | THiding	    (Src String)	    -- ^ hiding 
	    | THConstraint  (Src String)	    -- ^ hconstraint 
	    | TExtern	    (Src String)	    -- ^ extern 
	    | TModule	    (Src String)	    -- ^ module 
            | TXModule      (Src String)            -- ^ xmodule
	    | TImport	    (Src String)	    -- ^ import 
	    | TAs	    (Src String)	    -- ^ as 
	    | TQualified    (Src String)	    -- ^ qualified 
	    | TPrimitive    (Src String)	    -- ^ primitive 
	    | TData	    (Src String)	    -- ^ data 
	    | TType	    (Src String)	    -- ^ type 
	    | TForall	    (Src String)	    -- ^ forall 
	    | TSemicolon			    -- ^ `;'
	    | TLBrace				    -- ^ `{'
	    | TRBrace				    -- ^ '}'
	    | TEquals	    (Src String)	    -- ^ `='
	    | TBackslash    (Src String)	    -- ^ `\\'
	    | TArrow	    (Src String)	    -- ^ `->'
	    | TIf	    (Src String)	    -- ^ if 
	    | TThen	    (Src String)	    -- ^ then
	    | TElse	    (Src String)	    -- ^ else
	    | TLet	    (Src String)	    -- ^ let
	    | TIn	    (Src String)	    -- ^ in
	    | TDo	    (Src String)	    -- ^ do
	    | TCase	    (Src String)	    -- ^ case
	    | TOf	    (Src String)	    -- ^ of
	    | TWhere	    (Src String)	    -- ^ where
	    | TLParen	    (Src String)	    -- ^ `('
	    | TRParen	    (Src String)	    -- ^ `)'
	    | TLBracket	    (Src String)	    -- ^ `['
	    | TRBracket	    (Src String)	    -- ^ `]'
	    | TCont	    (Src String)	    -- ^ `..'
	    | TUnderscore   (Src String)	    -- ^ `_'
	    | TImpl	    (Src String)	    -- ^ `=>'
	    | TPropArrow    (Src String)	    -- ^ `==>'
	    | TSimpArrow    (Src String)	    -- ^ `<=>'
	    | TComma				    -- ^ `,'
	    | TDot				    -- ^ `.'
	    | TAt	    (Src String)	    -- ^ `@'
	    | TBar	    (Src String)	    -- ^ `|'
	    | TLArrow	    (Src String)	    -- ^ `<-'
	    | TAnn	    (Src String)	    -- ^ `::'
	    | TEAnn	    (Src String)	    -- ^ `:::'
	    | TRAnn	    (Src String)	    -- ^ `:*:'
	    | TTrue	    (Src String)	    -- ^ True
	    | TFalse	    (Src String)	    -- ^ False
	    | TAsterisk	    (Src String)	    -- ^ `*'
	    | TQuery	    (Src String)	    -- ^ `::?'
	    | TQuestion     (Src String)            -- ^ '?'

            | TConstraint   (Src String)            -- ^ constraint

	    | TLayoutBlock Int	-- ^ Indicates start of a block. (inserted
				--   after let, where, do, of.)
	    | TLayoutFirst Int	-- ^ First text column in a new line.
	    
	    | Teof		 -- ^ The EOF that Happy sees
	    | Tend (Src ())	 -- ^ The EOF that records the last text position
            | TFunc (Src String) -- ^ 'TF_' Indicates following id token is an Associated
                                 --   Type Synonym. 
	      deriving Eq

----------------------------------------

instance Show Token where
    show tok = case tok of
	TId    (str, _)	-> str -- ++ "-id"
	TConId (str, _)	-> str
	TIId   (str, _)	-> str -- ++ "-infix"
	TInt ((_,str),_)-> str
	TFloat ((_,str,_),_)-> str
	TChar (char, _)	-> show char
	TStr (str, _)	-> str
	TMinus _	-> "-" -- ++ "minus"
	TRule _		-> "rule" 
	TOverload _	-> "overload"
	TClass _	-> "class"
	TInstance _	-> "instance"
	TDeriving _	-> "deriving"
	TInfix _	-> "infix"
	TInfixl _	-> "infixl"
	TInfixr _	-> "infixr"
	THiding _	-> "hiding"
	THConstraint _	-> "hconstraint"
	TExtern	_	-> "extern"
	TModule _	-> "module"
        TXModule _      -> "xmodule"
	TImport _	-> "import"
	TAs _		-> "as"
	TQualified _	-> "qualified"
	TPrimitive _    -> "primitive"
	TData _		-> "data"
	TForall	_	-> "forall"
	TSemicolon 	-> ";"
	TLBrace		-> "{"
	TRBrace		-> "}"
	TEquals	_	-> "="
	TBackslash _	-> "\\"
	TArrow _	-> "->"
	TIf _		-> "if"
	TThen _		-> "then"
	TElse _		-> "else"
	TLet _		-> "let"
	TIn _		-> "in"
	TDo _		-> "do"
	TCase _		-> "case"
	TOf _		-> "of"
	TWhere _	-> "where"
	TLParen	_	-> "("
	TRParen	_	-> ")"
	TLBracket _	-> "["
	TRBracket _	-> "]"
	TUnderscore _	-> "_"
	TImpl _		-> "=>"
	TPropArrow _	-> "==>"
	TSimpArrow _	-> "<==>"
	TComma		-> ","
	TDot 		-> "."
	TBar _ 		-> "|"
	TLArrow _	-> "<-"
	TAnn _		-> "::"
	TEAnn _		-> ":::"
	TRAnn _		-> ":*:"
	TAsterisk _	-> "*"
	TTrue _		-> "True!"
	TFalse _	-> "False!"
	TQuery _	-> "::?"
	TQuestion _	-> "?"
	TCont _		-> ".."
	TType _		-> "type"

	TAt _		-> "@"

        TConstraint _   -> "constraint"

	TLayoutBlock int    -> "LAYOUT{"++show int++"}"
	TLayoutFirst int    -> "LAYOUT<"++show int++">"
	Teof 		    -> "EOF"

	Tend _		-> "THE_END!"
        TFunc _         -> "@_"
	_		-> "<BUG: some token>"

----------------------------------------

instance AST.StdToken Token where

    tokenString = show

    tokenSrcPos t = case t of
	TId	     x -> snd x
        TConId	     x -> snd x
        TIId	     x -> snd x
        TInt	     x -> snd x
        TFloat	     x -> snd x
        TChar	     x -> snd x
        TStr	     x -> snd x
        TMinus	     x -> snd x
        TRule        x -> snd x
        TOverload    x -> snd x
        TClass	     x -> snd x
        TInstance    x -> snd x
        TDeriving    x -> snd x
	THiding	     x -> snd x
        THConstraint x -> snd x
        TExtern	     x -> snd x
        TModule	     x -> snd x
        TXModule     x -> snd x
        TImport	     x -> snd x
        TData	     x -> snd x
        TType	     x -> snd x
        TForall	     x -> snd x
        TEquals	     x -> snd x
        TBackslash   x -> snd x
        TArrow	     x -> snd x
        TIf	     x -> snd x
        TThen	     x -> snd x
        TElse	     x -> snd x
        TLet	     x -> snd x
        TIn	     x -> snd x
        TDo	     x -> snd x
        TCase	     x -> snd x
        TOf	     x -> snd x
        TWhere	     x -> snd x
        TLParen	     x -> snd x
        TRParen	     x -> snd x
        TLBracket    x -> snd x
        TRBracket    x -> snd x
        TCont	     x -> snd x
        TUnderscore  x -> snd x
        TImpl	     x -> snd x
        TPropArrow   x -> snd x
        TSimpArrow   x -> snd x
        TBar	     x -> snd x
        TLArrow	     x -> snd x
        TAnn	     x -> snd x
        TEAnn	     x -> snd x
        TRAnn	     x -> snd x
        TTrue	     x -> snd x
        TFalse	     x -> snd x
        TAsterisk    x -> snd x
        TQuery	     x -> snd x
	TQuestion    x -> snd x             
	Tend	     x -> snd x
        TConstraint  x -> snd x
        TFunc        x -> snd x
        _	       -> noSrcPos
