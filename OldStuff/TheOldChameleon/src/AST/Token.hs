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
-- | Contains a class for extracting information out of tokens, regardless of 
-- the specific parser and set of tokens in use. Also a data type which 
-- encapsulates all such Tokens.
--
--------------------------------------------------------------------------------

module AST.Token (
    Token(..), StdToken(..), noSrcPos, TokenStream
)
where

--------------------------------------------------------------------------------

-- | A token's position information: module, row, column.
type TokenSrcPos = (String, Int, Int)

-- | No specific src. position.
noSrcPos :: TokenSrcPos 
noSrcPos = ("", -1, -1)

class Show a => StdToken a where
    -- | Finds the position of the token in the source file.
    tokenSrcPos :: a -> TokenSrcPos

    -- | Returns a string representation of the token.
    tokenString :: a -> String

----------------------------------------

-- | A token, independent of a specific parser, with the above standard methods.
data Token = forall a. (Show a, StdToken a) => Token a

instance Show Token where
    show (Token t) = show t

-- | A stream full of tokens. (splash, splash)
type TokenStream = [Token]

instance StdToken Token where
    tokenSrcPos (Token t) = tokenSrcPos t
    tokenString (Token t) = tokenString t
