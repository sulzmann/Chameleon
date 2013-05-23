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
-- Implementor: J. Wazny
-- Maintainer : J. Wazny
--------------------------------------------------------------------------------
--
-- | Contains routines for re-ordering binding groups in dependency order.
-- INCOMPLETE!
--------------------------------------------------------------------------------

module AST.Reorder (
    reorderBindingGroups
) where

import List

import AST.Internal
import AST.CallGraph

--------------------------------------------------------------------------------

-- | Given a normalised callgraph, and a program, reorders all binding groups
--   (and members of binding groups) in dependency order. This is necessary
--   if we use a strict backend.
reorderBindingGroups :: NormCallGraph -> Prog -> IO Prog
reorderBindingGroups cg (Prog ms) = do
    ms' <- mapM (roModule cg) ms
    return (Prog ms')

roModule :: NormCallGraph -> Module -> IO Module
roModule cg (Module id xs is ds t) = do
    ds' <- roDecs cg ds
    return (Module id xs is ds' t)

----------------------------------------

roDecs :: NormCallGraph -> [Dec] -> IO [Dec]
roDecs cg ds = do
    let (vds, ods) = partition isValDec ds
    return (ods++vds)
