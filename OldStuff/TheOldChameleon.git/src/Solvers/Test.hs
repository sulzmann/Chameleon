{- Test.hs -- Tests the CHR solver + herbie with a good ol' leq/2 solver
   Copright (C) 2004 Gregory J. Duck

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA 
-}

module Main where

import Solvers.Herbrand
import Solvers.HsHerbie
import Solvers.CHR
import Solvers.CHRState
import Foreign.C
import List
import Data.FiniteMap
import Core.Justify

testGoal :: Herb s c => CInt -> Herbrand s (State c)
testGoal i = do
    leqstr <- doIO (newCString "Leq")
    leq <- cnst leqstr
    f <- var 
    goal0 <- testGoal' leq f f i
    createGoal goal0 (replicate (length goal0) noJust)

testGoal' :: Herb s c => c -> c -> c -> CInt -> Herbrand s [c]
testGoal' leq p f 0 = do
    leqpf <- construct leq [p,f]
    return [leqpf]
testGoal' leq p f i = do
    n <- var 
    leqpn <- construct leq [p,n]
    restgoal <- testGoal' leq n f (i-1)
    return (leqpn:restgoal)

testProg :: Herb s c => Herbrand s [Rule c]
testProg = do
    leqstr <- doIO (newCString "Leq")
    leq <- cnst leqstr
    eqstr <- doIO (newCString "=")
    eq <- cnst eqstr
    x <- var 
    y <- var 
    z <- var 
    leqxy <- construct leq [x,y]
    leqyx <- construct leq [y,x]
    leqyz <- construct leq [y,z]
    leqxz <- construct leq [x,z]
    leqxx <- construct leq [x,x]
    eqxy <- construct eq [x,y]
    return [
        SimpRule [leqxx] [] [],
        SimpRule [leqxy,leqyx] [eqxy] [noJust],
        PropRule [leqxy,leqyz] [leqxz] [noJust]
        ]

main = do
    store <- newStore
    final <- runHerbrand store (runCHR Failed (
        do prog0 <- doHerbrand testProg 
           prog1 <- doHerbrand (compileCHRs prog0)
           goal  <- doHerbrand (testGoal 25)
           putState goal
           derivation prog1
           getState))
    checkState final
    deleteStore store
--    printState final

checkState :: State Term -> IO ()
checkState st = case st of 
    Failed	     -> testFailed
    State _ [] _ _ _ -> testPassed
    _		     -> testFailed
  where
    testFailed = putStr "FAILED\n"
    testPassed = putStr "PASSED\n"

{-
printState :: State Term -> Herbrand State ()
printState Failed = doIO (putStr "Failed")
printState (State _ ustore _ _) = 
    printStore ustore

printStore :: UStore Term -> Herbrand State ()
printStore [] = do return ()
printStore ((Num (UCons _ _ cons) id):store) = do
    print_term cons
    printStore store
-}

