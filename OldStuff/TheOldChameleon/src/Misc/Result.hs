--------------------------------------------------------------------------------
--
-- Copyright (C) 2005 The Chameleon Team
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

module Misc.Result
where

import AST.SrcInfo
import Misc.Error
import Misc

--------------------------------------------------------------------------------
-- Another error monad (like E). This one carries more information, though.
-- Use it instead. (Since the pipeline will expect results in this form.)

data Result a b = Failure { resultErrors :: [Error], lastResult :: a }
		| Success { resultErrors :: [Error], result :: b }
    deriving (Show)

mkFailure :: Error -> a -> Result a b
mkFailure err a = Failure [err] a

mkSuccess :: b -> Result a b
mkSuccess b = Success [] b


-- a plain result is one where we don't care about any partial failure values
type SimpleResult b = Result () b

simpleFailure :: [Error] -> SimpleResult b
simpleFailure es = Failure es ()


instance Monad (Result a) where

  -- (>>=) :: Result a -> (a -> Result b) -> Result b
  m >>= k = case m of
		Failure e a  -> Failure e a
		Success e b  -> case k b of
				Failure e' a -> Failure (e'++e) a
				Success e' b -> Success (e'++e) b

  -- return :: a -> Result a
  return x = Success [] x
 
  fail s = let e = mkError anonSrcInfo s
	   in  trace ("note: Don't call Result's fail method") (unsafeFailure e)

unsafeFailure :: Error -> Result a b
unsafeFailure e = Failure [e] (bug "unsafeFailure")

isSuccess, isFailure :: Result a b -> Bool
isSuccess (Success {}) = True
isSuccess _	       = False

isFailure (Failure {}) = True
isFailure _	       = False

