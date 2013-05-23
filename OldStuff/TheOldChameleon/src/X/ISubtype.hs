------------------------------------------------------
-- The Subtype interface                            --
------------------------------------------------------
module X.ISubtype where

import X.IAST

class Monad m => Env m e | m -> e where
    newName :: m String
    check :: e -> m (Maybe String)
    add :: (e,String) -> m ()
    del :: (e,String) -> m ()
    wishT :: e -> m ()
    wishF :: e -> m ()

class UCast s t where
    ucast :: (AST e p, Env m (s,t)) => s -> t -> m e

class NUCast s t where
    nucast :: (AST e p, Env m (s,t)) => s -> t -> m e

class DCast s t where
    dcast :: (AST e p, Env m (s,t)) => s -> t -> m e

class NDCast s t where
    ndcast :: (AST e p, Env m (s,t)) => s -> t -> m e

class Norm t where
    tnorm :: (AST e p) => t -> (t,e,e)