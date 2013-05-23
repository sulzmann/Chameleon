{-# OPTIONS -cpp #-}
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
-- Global configuration data. 
-- (i.e. not specific to any module or subsystem)
--
-- Also contains certain system-wide defaults.
--------------------------------------------------------------------------------

module Config.Global (
    Options(..), flagsToOptions, VerbLevel(..), CompileStage(..),
    BackEnd(..), InfScheme(..), Stop(..),
    defaultOutputFilename, defaultModuleName, defaultFilenameExtension, 
    defaultBackEnd, schemeFilenameExtension, lvmFilenameExtension,
    pathSep, moduleToPath, mkPath, inPath, underInstallPath,

    implicitImports
)
where

import List
import Maybe

import Config.Flags

--------------------------------------------------------------------------------

data Options = Options { 
	colourText  :: Bool,
	verbosity   :: VerbLevel,
	inputFiles  :: [String],
	outputFile  :: String,
	modulePaths :: [FilePath],  -- directories to look in for modules
	backend	    :: BackEnd,
	importImplicit :: Bool,
	checkKinds :: Bool,
        checkIntSyntax :: Bool,
        xhaskellExt    :: Bool,
	infScheme   :: InfScheme,
	lastStage   :: CompileStage, -- the last stage to run before stopping
        mimicGHC :: Bool }
    deriving (Show)

-- level of verbosity: 0 = quiet (default)
--		       1 = informative 
--		       2 = verbose
--		       3 = extremely verbose (includes debugging output)
newtype VerbLevel = VerbLevel Int
    deriving (Eq, Ord, Show)

-- Name of the compiler's stages/phases
-- NOTE: These refer to stages when processing the primary module (i.e. the one
--	 actually specified by the user), not any of the stages performed when
--	 processing modules that are depended upon.
data CompileStage = BatchModules
		  | LoadSrc
		  | ParseSrc
		  | CheckExternal
		  | Desugar
		  | AnalyseInternal
		  | ValidataKinds
		  | ValidateTypes
		  | AllDone
    deriving (Eq, Ord, Enum, Show)

-- Indicates which back end to use.
-- NoBackEnd: produces empty target files
-- SchemeBackEnd: the scheme source back end
data BackEnd = NoBackEnd
	     | SchemeBackEnd
	     | SchemeLazyBackEnd
             | LvmBackEnd
    deriving (Eq, Show)

-- Represents which (HM) inference scheme to use
data InfScheme = W_Based
	       | CHR_Based
    deriving (Eq, Show)

-- A general-purpose flag
data Stop = DontStop
	  | AlwaysStop
	  | MaybeStop
    deriving (Eq, Show)

--------------------------------------------------------------------------------

-- converts command line flags to options (updating standard options)
flagsToOptions :: [Flag] -> Options
flagsToOptions fs = 
    let ins   = [ f | InputFile f <- fs ]
	-- NOTE: we've already checked that there's only one output file
	out   = let os = [ f | OutputFile f <- fs ]
		    -- if no output is specified, use default
		    -- NOTE: later we use `stdout' if the filename is empty
		    f | StdOut `elem` fs = ""
		      | null os          = defaultOutputFilename
		      | otherwise	 = head os
		in  f
		
	noCol = NoColour `elem` fs

	verb  = let vs = [ v | Verbose v <- fs ]
		in  VerbLevel $ if null vs then 0 else head vs

	back = let bs = [ s | BackEnd s <- fs ]
	       in  if null bs then SchemeLazyBackEnd -- NoBackEnd
			      else let backends = 
					[ ("none", NoBackEnd)
					, ("scheme", SchemeBackEnd)
					, ("scheme-lazy", SchemeLazyBackEnd)
					, ("lvm", LvmBackEnd)
                                        ]
				   in  fromJust (lookup (head bs) backends)

	imp = and [ b | ImportImplicit b <- fs ]

	vk  = and [ b | CheckKinds b <- fs ]

        intCheck = and [ b | CheckIntSyntax b <- fs]

	-- NOTE: we already know there's only one final phase specified
	end | JustDesugar `elem` fs    = Desugar
	    | JustInferTypes `elem` fs = ValidateTypes
	    | otherwise = AllDone

        mimic = GHCStyleKinds `elem` fs

        xhaskell = XHaskellExt `elem` fs

	inf_scheme | CLPTypeInference `elem` fs = CHR_Based
		   | otherwise = W_Based

    in  stdOptions { colourText = not noCol,
		     verbosity  = verb,
		     inputFiles = ins,
		     outputFile = out,
		     backend    = back,
		     importImplicit = imp,
		     checkKinds = vk,
                     checkIntSyntax = intCheck,
                     xhaskellExt  = xhaskell,
		     lastStage  = end, 
                     mimicGHC = mimic,
		     infScheme = inf_scheme }

stdOptions :: Options
stdOptions = Options { colourText  = True,
		       verbosity   = VerbLevel 0,
		       inputFiles  = [],
		       outputFile  = defaultOutputFilename,
		       modulePaths = [".", libraryPath],
		       backend	   = defaultBackEnd,
		       importImplicit = True,
		       checkKinds  = True,
                       checkIntSyntax = True,
                       xhaskellExt    = False,
		       lastStage      = AllDone, 
                       mimicGHC = False,
		       infScheme = W_Based }


--------------------------------------------------------------------------------

defaultOutputFilename = "output"
defaultModuleName = "Main"

defaultBackEnd = NoBackEnd -- SchemeBackEnd
defaultFilenameExtension = ".ch"
schemeFilenameExtension = ".scm"
lvmFilenameExtension = ".lvm"
pathSep = "/"

mkPath :: [FilePath] -> FilePath
mkPath ps = concat (intersperse pathSep ps) ++ pathSep

inPath :: [FilePath] -> String -> FilePath
inPath ps fn = mkPath ps ++ pathSep ++ fn

moduleToPath :: String -> FilePath
moduleToPath m = rep m
  where
    rep "" = ""
    rep ('.':cs) = pathSep ++ rep cs
    rep (c:cs)   = c : rep cs

--------------------------------------------------------------------------------

installPath :: String
installPath = INSTALL_PATH

libraryPath :: String
libraryPath = installPath ++ mkPath ["lib"]

underInstallPath :: FilePath -> FilePath
underInstallPath fp = installPath ++ pathSep ++ fp

--------------------------------------------------------------------------------

-- Modules which are imported implicitly into each other module.
implicitImports :: [String]
implicitImports = ["Chameleon.Primitive"]
