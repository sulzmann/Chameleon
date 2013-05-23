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
--
--
--------------------------------------------------------------------------------

module Misc.Error 
where

import Misc
import AST.SrcInfo

--------------------------------------------------------------------------------
-- NOTE: The error message will not be further processed. It should already be
--	 in its final form. The position information is for use by a more
--	 advanced tool (like Typo) which may be able to indicate the source 
--	 position somehow. 

type Msg = String


-- Fatal errors demand eventually terminating the system. They can usually be 
-- overlooked in the short term, and accumulated, before being reported all
-- at once.
--
-- NonFatal errors are really just warnings. Execution can continue as normal.
--
-- SuperFatal errors are fatal errors which occur before a source file can be
-- loaded. We distinguish these from Fatal errors since they imply that any
-- source information contained in the error report is nonsensical.
--
-- NOTE: We sometimes refer to both Fatal and SuperFatal errors as `critical'.
data Severity = SuperFatal
	      | Fatal	  
	      | NonFatal  
    deriving (Eq, Show, Ord)

data Error    = Error Severity SrcInfo Msg
    deriving (Show)

errorSeverity :: Error -> Severity
errorSeverity (Error s _ _) = s

-- (==) is defined this way so that we can easily filter out multiple errors
-- from the exact same location.
instance Eq Error where
    (Error _ s1 _) == (Error _ s2 _) = s1 == s2

-- This allows us to easily sort errors based on severity.
instance Ord Error where
    compare (Error s1 _ _) (Error s2 _ _) = compare s1 s2

mkError, mkWarning :: HasSrcInfo a => a -> Msg -> Error
mkError   = Error Fatal . getSrcInfo
mkWarning = Error NonFatal . getSrcInfo

mkSuperFatalError :: Msg -> Error
mkSuperFatalError = Error SuperFatal anonSrcInfo

notAnError :: Error
notAnError = Error NonFatal anonSrcInfo "This is not an error, don't report it!"

--------------------------------------------------------------------------------
-- A class of monads for handling errors, specifically with the 
-- ability to accumulate error messages (containing position information.)

class AccumError m where
    -- adds a new error message to the list
    addErrorMsg :: HasSrcInfo a => a -> Msg -> m ()

-- add a message without position information
addAnonErrorMsg :: AccumError m => Msg -> m ()
addAnonErrorMsg m = addErrorMsg anonSrcInfo m

--------------------------------------------------------------------------------

isCritical :: Severity -> Bool
isCritical NonFatal = False
isCritical _	    = True

isSuperFatal :: Severity -> Bool
isSuperFatal SuperFatal = True
isSuperFatal _		= False

anyCriticalErrors :: [Error] -> Bool
anyCriticalErrors es = not (null [ e | e@(Error s _ _) <- es, isCritical s ])

-- reports all messages to the terminal, and exits
reportErrorsAndExit :: [Error] -> a
reportErrorsAndExit es = exit (errorsToString es)

-- reports all errors, and continues (usually this would only be invoked for
-- non-fatal errors)
reportErrors :: [Error] -> IO ()
reportErrors [] = return ()
reportErrors es = putStrLn (errorsToString es)

errorsToString :: [Error] -> String
errorsToString = doubleNewlines . errorsToStrings

errorsToStrings :: [Error] -> [String]
errorsToStrings es = [ m | Error _ _ m <- es ]
