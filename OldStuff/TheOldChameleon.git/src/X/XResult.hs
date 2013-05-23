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
--
-------------------------------------------------------------------------------

module X.XResult where

import AST.Internal as I
import AST.SrcInfo
import Core.Types as C




-- Represent the XHaskell Translation result

data XResult a = XSuccess { resultErrors :: [XError], result :: a }
               | XFailure { resultErrors :: [XError] }



data XError = AnnErr { theid :: Id } 
            | SubtypeErr { src :: SrcInfo
                         , sub :: I.Type
                         , sup :: I.Type
                         }
	    | NonExhaustiveErr { src :: SrcInfo
			       , aty :: I.Type
			       , pty :: I.Type
			       }
            | UnboundVarErr { theid :: Id }	
	    | FunExpErr { exp :: Exp }
	    | UnboundConErr { theid :: Id }

instance Monad XResult where

  -- (>>=) :: XResult a -> (a -> XResult b) -> XResult b
  m >>= k = case m of
		XFailure e -> XFailure e
		XSuccess e b  -> case k b of
				 XFailure e' -> XFailure (e'++e)
				 XSuccess e' b -> XSuccess (e'++e) b

  -- return :: a -> XResult a
  return x = XSuccess [] x
 

isXSuccess, isXFailure :: XResult a -> Bool
isXSuccess (XSuccess {}) = True
isXSuccess _	         = False

isXFailure (XFailure {}) = True
isXFailure _	        = False

