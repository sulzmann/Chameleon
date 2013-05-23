{------------------------------------------------------------------------
  The Core Assembler.

  Copyright 2001, Daan Leijen. All rights reserved. This file
  is distributed under the terms of the GHC license. For more
  information, see the file "license.txt", which is included in
  the distribution.
------------------------------------------------------------------------}

--  $Id$
module AsmOptimize( asmOptimize ) where

import Asm
import AsmInline ( asmInline )

{---------------------------------------------------------------
  asmOptimize
---------------------------------------------------------------}
asmOptimize :: AsmModule -> AsmModule
asmOptimize mod
  = asmInline mod