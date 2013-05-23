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
-- Typo - the interactive type debugger.
--
-- The Main module is responsible for shunting information back and forth
-- between the interface, and the core, via the system state (established in
-- Core.)
--
--------------------------------------------------------------------------------

module Main
where

import System

import Config.Global
import Config.CmdLine
import System.Typo.Core
import System.Typo.Interface

--------------------------------------------------------------------------------

main :: IO ()
main = do 
    as <- getArgs
    let fs   = parseCmdLineArgs as
	opts = flagsToOptions fs
    startup opts

--------------------------------------------------------------------------------

startup :: Options -> IO ()
startup opts = do
    state <- initialState opts
    interface state
