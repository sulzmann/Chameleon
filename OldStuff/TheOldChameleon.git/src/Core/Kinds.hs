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
-- Kinds: inference and checking
-- This module provides an interface between the kind stuff and the rest of the
-- system.
--
--------------------------------------------------------------------------------

module Core.Kinds (
   module Core.Kinds.Inference, module Core.Kinds.Checking, pile
) where

import Core.Kinds.Inference
import Core.Kinds.Checking
import qualified AST.Internal as AST

--------------------------------------------------------------------------------

--testPrint :: Display a => a -> IO ()
--testPrint ds = do putStr ((display ds False) ++ "\n")

pile :: AST.Prog -> IO [AST.Dec]
pile (AST.Prog m) = pileDecs m

pileDecs :: [AST.Module] -> IO [AST.Dec]
pileDecs [x] = do d <- getDecs x
                  return d
pileDecs (x:xs) = do n <- pileDecs xs
                     m <- getDecs x
                     return (m ++ n)

getDecs :: AST.Module -> IO [AST.Dec]
getDecs (AST.Module _ _ _ dec _) = return dec
