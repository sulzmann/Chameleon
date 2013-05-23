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
-- Contains routines for reading and writing files, which generate meaningful
-- error message in the event of some failure.
-- NOTE: Stuff like chasing module dependencies, does not belong here.
--
--------------------------------------------------------------------------------

module Misc.Files (
    openFileWrite, openFileRead,
    closeHandle, readFileContents, writeFileContents, writeString,
    readFileContentsSrc
)
where

import IO

import AST.SrcInfo
import Misc
import Misc.ErrorMsg

--------------------------------------------------------------------------------

-- opens a file for writing
openFileWrite :: FilePath -> IO (E Handle)
openFileWrite f = eOpenFile f WriteMode `catch` handleFileError f

-- opens a file for writing
openFileRead :: FilePath -> IO (E Handle)
openFileRead f = eOpenFile f ReadMode `catch` handleFileError f

-- closes a handle
closeHandle :: Handle -> IO ()
closeHandle = hClose

----------------------------------------
-- read and write files -- weird code, clean it up.


-- Reads input from the named file - uses the attached source information when
-- producing an error report.
readFileContentsSrc :: FilePath -> SrcInfo -> IO (E String)
readFileContentsSrc f info = (do 
    eh <- eOpenFile f ReadMode 
    case eh of
	Err e  -> return (Err e)
	Succ h -> do str <- readInput f h
		     hClose h
		     return str) `catch` handleFileErrorSrc f info


-- Reads input from the named file.
readFileContents :: FilePath -> IO (E String)
readFileContents f = (do 
    eh <- eOpenFile f ReadMode 
    case eh of
	Err e  -> return (Err e)
	Succ h -> do str <- readInput f h
		     hClose h
		     return str) `catch` handleFileError f

writeString :: FilePath -> Handle -> String -> IO (E ())
writeString fn h str = 
    (hPutStr h str >> return (Succ ())) `catch` handleFileError fn

-- writes the given string to a file
writeFileContents :: FilePath -> String -> IO (E ())
writeFileContents f str = (do
    eh <- eOpenFile f WriteMode
    case eh of
	Err e  -> return (Err e)

	Succ h -> do eHPutStr h str 
		     hClose h
		     return (return ())) `catch` handleFileError f
  where
    eHPutStr h str = hPutStr h str >> return (Succ ())


eOpenFile f m = do h <- openFile f m
		   return (Succ h)

readInput :: FilePath -> Handle -> IO (E String)
readInput f h = eHGetContents h `catch` handleFileError f
  where 
    eHGetContents h = do
	strs <- read h
	return (Succ (unlines strs))

    read h = do 
	end <- hIsEOF h
	if end then return [""]
	       else do x  <- hGetLine h
		       xs <- read h
		       return (x:xs)

--------------------------------------------------------------------------------

-- A simple exception handler for file operations. It takes the name of the 
-- file being worked on and in the event of an error prints an appropriate 
-- message and exits (failure).
handleFileError :: FilePath -> IOError -> IO (E a)
handleFileError f x = handleFileErrorSrc f anonSrcInfo x

handleFileErrorSrc :: FilePath -> SrcInfo -> IOError -> IO (E a)
handleFileErrorSrc f info x
    | isAlreadyInUseError x = err ("File `" ++ f ++ "' is already in use")
    | isDoesNotExistError x = err ("File `" ++ f ++ "' does not exist")
    | isPermissionError   x = err ("You do not have permission to " ++
					   "access file `" ++ f ++ "'")
    | otherwise             = err ("Cannot access file `" ++ f ++ "'")
  where   
    err str | info == anonSrcInfo ||
	      info == builtInSrcInfo = return (Err (errorMsgNoSrc [str]))
	    | otherwise = return (Err (errorMsgLine info [str]))
