------------------------------------------------------
-- The AST interface                                --
------------------------------------------------------
module X.IAST where
    
class AST e p | e -> p, p -> e where
-- Expressions :: = 
    eApp :: e -> e -> e                                 -- (e e)		|
    eAbs :: p -> e -> e                      -- \p -> e		|
    eCase :: e -> [(p,e)] -> e		-- case e of [p->e]_i   |
    eVar :: String -> e                                 -- x			|
    eCon :: String -> e                                 -- k e			|
    eTup :: [e] -> e                                    -- (e,...,e)            |
    eInt :: Integer -> e                                -- i			|
    eStr :: String -> e                                 -- s			|
    eLet :: [(p,e)] -> e -> e                -- let [p=e]_i in e	|
-- Exp Short-hands :: = 
    ePair :: e -> e -> e                                -- (e,e)		|
    eL	   :: e -> e                                    -- L e			|  
    eR	   :: e -> e                                    -- R e			|
    eCons  :: e -> e -> e                               -- e:e			|
    eNil   :: e                                         -- []			|
    eJust  :: e -> e                                    -- Just e               |
    eNothing :: e                                       -- Nothing              |
    eUndefined :: e                                     -- Undefined            |
    eError     :: String -> e                           -- error                |
    ePlus      :: e                                     -- +    
-- Patterns    :: =			
    pVar :: String -> p                                 -- x			
    pCon :: String -> [p] -> p                          -- k p			|
    pTup :: [p] -> p                                    -- (p,...,p)            |
    pInt :: Integer -> p                                -- i                    | 
-- Pat Short-hands :: =
    pPair :: p -> p -> p                                -- (p,p)		|
    pL :: p -> p                                        -- L p			|
    pR :: p -> p                                        -- R p			|
    pCons :: p -> p -> p                                -- (p:p)		|
    pNil :: p                                           -- []                   |
    pJust :: p -> p                                     -- Just p               |
    pNothing :: p                                       -- Nothing              |
    pWildcard :: p                                      -- _                    