{------------------------------------------------------------------------
  The Core Assembler.

  Copyright 2001, Daan Leijen. All rights reserved. This file
  is distributed under the terms of the GHC license. For more
  information, see the file "license.txt", which is included in
  the distribution.
------------------------------------------------------------------------}

--  $Id$

module LvmPretty( lvmPretty ) where

import PPrint
import Lvm
import InstrPretty  ( instrPretty )
import ModulePretty ( modulePretty )

lvmPretty :: LvmModule -> Doc
lvmPretty mod
  = modulePretty instrPretty mod
