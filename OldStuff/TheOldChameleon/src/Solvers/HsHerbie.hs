--------------------------------------------------------------------------------
-- Herbie.hs -- Haskell interface to herbie
-- Copright (C) 2004 Gregory J. Duck
-- (Modified/Improved by The Chameleon Team)
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program; if not, write to the Free Software
-- Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA 
--
--------------------------------------------------------------------------------

module Solvers.HsHerbie (
    Store, Term, print_term, eqCString) 
where

import Monad
import Foreign
import Foreign.C

import Solvers.Herbrand

type Store = Ptr ()
type Term  = Ptr ()

instance Herb Store Term where
    newStore = new_store
    deleteStore = delete_store
    unify = herbie_unify
    match = herbie_match
    eqeq = herbie_eqeq
    variant = herbie_variant
    skolemise = herbie_skolemise
    cnst = herbie_construct_const
    app = herbie_construct_app
    var = herbie_fresh_var
    cnstName = herbie_cnst_name
    appArg = herbie_app_arg
    isVar = herbie_is_var
    isCnst = herbie_is_cnst
    isApp = herbie_is_app
    wasVar = herbie_was_var
    deref = herbie_deref
    ground = herbie_is_ground
    share = herbie_share_terms
    createCP = herbie_create_choice_point
    rewind = herbie_rewind
    rename = herbie_rename
    setFlag = herbie_set_flag
    printTerm = herbie_print_term
    construct = herbie_construct
    functor = herbie_functor
    arg = herbie_arg

foreign import ccall "eq_string" eqCString :: CString
foreign import ccall "new_store" new_store :: IO Store
foreign import ccall "delete_store" delete_store :: Store -> IO ()
foreign import ccall "construct_const" construct_const :: Store -> CString -> IO Term
foreign import ccall "construct_app" construct_app :: Store -> Term -> Term -> IO Term
foreign import ccall "fresh_var" fresh_var :: Store -> IO Term
foreign import ccall "unify_term_term" low_level_unify :: Store -> Term -> Term -> IO CInt
foreign import ccall "match_term_term" low_level_match :: Store -> Term -> Term -> IO CInt
foreign import ccall "entailment_term_term" low_level_entailment :: Store -> Term -> Term -> IO CInt
foreign import ccall "variant_term_term" low_level_variant_check :: Store -> Term -> Term -> IO CInt
foreign import ccall "do_skolemise" do_skolemise :: Store -> Term -> IO ()
foreign import ccall "is_var" is_var :: Term -> IO CInt
foreign import ccall "is_const" is_cnst :: Term -> IO CInt
foreign import ccall "is_app" is_app :: Term -> IO CInt
foreign import ccall "was_var" was_var :: Term -> IO CInt
foreign import ccall "deref" do_deref :: Term -> IO Term
foreign import ccall "app_arg" app_arg :: Term -> CInt -> IO Term
foreign import ccall "get_code_symbol" get_symbol :: Term -> IO CString
foreign import ccall "ground" is_ground :: Term -> IO CInt
foreign import ccall "share_variables" share_variables :: Term -> Term -> IO CInt
foreign import ccall "print_term" print_term :: Term -> IO ()
foreign import ccall "create_choice_point" create_choice_point :: Store -> IO ChoicePointId
foreign import ccall "rewind_trail" rewind_trail :: Store -> ChoicePointId -> IO ()
foreign import ccall "copy_term" copy_term :: Store -> Term -> IO Term
foreign import ccall "set_flag" set_flag :: Store -> CInt -> CInt -> IO ()

c_int_to_bool :: CInt -> Bool
c_int_to_bool 0 = False
c_int_to_bool _ = True

c_int_to_unify_code :: CInt -> UnifyStatus
c_int_to_unify_code 0 = Success
c_int_to_unify_code 1 = MismatchFail
c_int_to_unify_code 2 = OccursFail
c_int_to_unify_code 3 = MatchingFail

flag_state_to_c_int :: FlagState -> CInt
flag_state_to_c_int On  = 1
flag_state_to_c_int Off = 0

-- WARNING: Must be consistent with the macros in herbie.c!
flag_to_c_int :: HerbrandFlag -> CInt
flag_to_c_int NoRewindHeap  = 0x00000001
flag_to_c_int NoOccursCheck = 0x00000002
flag_to_c_int NoTrail       = 0x00000004

herbie_unify :: Term -> Term -> Herbrand Store UnifyStatus
herbie_unify term1 term2 = do
    store <- getStore
    result <- doIO (low_level_unify store term1 term2)
    return (c_int_to_unify_code result)

herbie_match :: Term -> Term -> Herbrand Store UnifyStatus
herbie_match term1 term2 = do
    store <- getStore
    result <- doIO (low_level_match store term1 term2)
    return (c_int_to_unify_code result)
                
herbie_eqeq :: Term -> Term -> Herbrand Store UnifyStatus
herbie_eqeq term1 term2 = do
    store <- getStore
    result <- doIO (low_level_entailment store term1 term2)
    return (c_int_to_unify_code result)

herbie_variant :: Term -> Term -> Herbrand Store UnifyStatus
herbie_variant term1 term2 = do
    store <- getStore
    result <- doIO (low_level_variant_check store term1 term2)
    return (c_int_to_unify_code result)

herbie_skolemise :: Term -> Herbrand Store ()
herbie_skolemise term = do
    store <- getStore
    doIO (do_skolemise store term)

herbie_construct_const :: CString -> Herbrand Store Term
herbie_construct_const name = do
    store <- getStore
    doIO (construct_const store name)

herbie_construct_app :: Term -> Term -> Herbrand Store Term
herbie_construct_app arg1 arg2 = do
    store <- getStore
    doIO (construct_app store arg1 arg2)

herbie_fresh_var :: Herbrand Store Term
herbie_fresh_var = do
    store <- getStore
    doIO (fresh_var store)

herbie_cnst_name :: Term -> Herbrand Store CString
herbie_cnst_name term = do
    doIO (get_symbol term)

herbie_app_arg :: Term -> CInt -> Herbrand Store Term
herbie_app_arg app argno = do
    doIO (app_arg app argno)

herbie_is_var :: Term -> Herbrand Store Bool
herbie_is_var term = do
    result <- doIO (is_var term)
    return (c_int_to_bool result)

herbie_is_cnst :: Term -> Herbrand Store Bool
herbie_is_cnst term = do
    result <- doIO (is_cnst term)
    return (c_int_to_bool result)

herbie_is_app :: Term -> Herbrand Store Bool
herbie_is_app term = do
    result <- doIO (is_app term)
    return (c_int_to_bool result)

herbie_was_var :: Term -> Herbrand Store Bool
herbie_was_var term = do
    result <- doIO (was_var term)
    return (c_int_to_bool result)

herbie_deref :: Term -> Herbrand Store Term
herbie_deref term = 
    doIO (do_deref term)

herbie_is_ground :: Term -> Herbrand Store Bool
herbie_is_ground term = do
    result <- doIO (is_ground term)
    return (c_int_to_bool result)

herbie_share_terms :: Term -> Term -> Herbrand Store Bool
herbie_share_terms term1 term2 = do
    result <- doIO (share_variables term1 term2)
    return (c_int_to_bool result)

herbie_create_choice_point :: Herbrand Store ChoicePointId
herbie_create_choice_point = do
    store <- getStore
    doIO (create_choice_point store)

herbie_rewind :: ChoicePointId -> Herbrand Store ()
herbie_rewind id = do
    store <- getStore
    doIO (rewind_trail store id)

herbie_rename :: Term -> Herbrand Store Term
herbie_rename term = do
    store <- getStore
    doIO (copy_term store term)

herbie_set_flag :: HerbrandFlag -> FlagState -> Herbrand Store ()
herbie_set_flag flag state  = do
    store <- getStore
    doIO (set_flag store (flag_to_c_int flag) (flag_state_to_c_int state))

herbie_print_term :: Term -> Herbrand Store ()
herbie_print_term term = doIO (print_term term)

herbie_construct :: Term -> [Term] -> Herbrand Store Term
herbie_construct f []         = return f
herbie_construct f args@(_:_) = do
    nargs <- herbie_make_args args
    herbie_construct_app f nargs

herbie_make_args :: [Term] -> Herbrand Store Term
herbie_make_args []         = do
    emptystr <- doIO (newCString "")
    herbie_construct_const emptystr
herbie_make_args (arg:args) = do
    nargs <- herbie_make_args args
    herbie_construct_app arg nargs

herbie_functor :: Term -> Herbrand Store (Term,CInt)
herbie_functor term = do
    term_derefed <- doIO (do_deref term)
    atom <- isCnst term_derefed
    if atom
      then do
         return (term_derefed,0)
      else do
         f <- appArg term_derefed 0
         f_derefed <- doIO (do_deref f)
         args <- appArg term_derefed 1
         noargs <- herbie_count_args args
         return (f_derefed,noargs)

herbie_count_args :: Term -> Herbrand Store CInt
herbie_count_args args = do
    atom <- isCnst args
    if atom
      then do
        return 0
      else do
        nargs <- appArg args 1
        len0 <- herbie_count_args nargs
        return (1+len0)

herbie_arg :: Term -> CInt -> Herbrand Store Term
herbie_arg c argno = do
    if argno == 0
      then do
        appArg c 0
      else do
        nc <- appArg c 1
        herbie_arg nc (argno-1)

