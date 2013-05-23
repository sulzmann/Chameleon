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
-- | Miscellaneous functions for parsing Chameleon (includes parser monad)
--
-- FIXME: 
-- 
-- * The parse errors that are detected by functions in this module 
--   (when converting a parsed value into some other value e.g. type into
--   a type class constraint) are terrible. No source position is given.
--------------------------------------------------------------------------------

module AST.ChParser.ParserMisc (
    P(), 
    TokenInfo,
    
    getState, setState,
    nextToken, teof, setStream, setOrigStream, tokensDone,
    setInput, getInput, ckHandleLayout, tokensAvailable, ckModImportMode,
    
    incColNum, addColNum, incLineNum, resetColNum, tabColNum,
    updateTokPos, getPos, getTokRow, getTokCol, getColNum, getLineNum, 
    getFileName, getPrevInput, getPrevToken, 
    mkPosToken, mkStdPosToken, dontHandleLayout, dontExitOnFail,
    dropContextEnd, useModImportMode, cleanupTokensImport,

    mkNode, mkNodes, mkNode2, mkNode3, mkNode0,
    mkNestedNode, mkNestedNode2, mkNestedNode3, mkNestedNode4,
    extractSrc, isTruePred, isFalsePred, mkTrueEqPrim, mkFalseEqPrim,
    typeToPred, tupToCtxt, addInfixParens, expToPat,
    
    runP, runPConf
)
where

import Misc
import Misc.Error
import Misc.Result
import AST.External
import qualified AST.Token as AST
import AST.ChParser.Tokens
import AST.SrcCommand
import AST.SrcInfo

-- import IOExts
import List

--------------------------------------------------------------------------------

-- FIXME: this description looks bogus (out of date)
--
-- input: current string
-- prevInput: stream before last token was removed (used for error reports)
-- noToken: True if no token has yet been read on the current line
-- layoutCols: stack of the layout contexts
-- indentToken: True if the previous token introduces a new layout block
-- exitOnFail: if True, bail to OS in event of a parse error
-- lineNum: current line number of stream
-- colNum:  current column number of stream
-- handleLayout: if True, the lexer will do a layout-removing transformation on
--		 the input stream
-- prevColNum: column of previous token in stream (used for error reports)
-- label: next label for AST annotation
data State = MkState {input :: String, 
		      prevInput :: String,
		      noToken :: Bool, 
		      layoutCols :: [Int], 
		      indentToken :: Bool,
		      exitOnFail :: Bool,
		      linenum :: Int, 
		      colnum :: Int,
		      tokRow :: Row, 
		      tokCol :: Col,
		      label :: UniqueNum,
		      handleLayout :: Bool,
		      tokensReady :: Bool, 
		      prevToken :: TokenInfo,
		      stream :: [TokenInfo],
		      origStream :: [TokenInfo],
		      commands :: [SrcCommand],
		      filename :: String, 
		      modImportMode :: Bool }	
    deriving Show

-- the parser monad, carries around the parser's state
newtype P a = P (State -> SimpleResult (State, a))

type TokenInfo = (Token, Row, Col)

instance Monad P where
    
    -- return :: a -> P a
    return a = P (\st -> return (st, a))
    
    -- (>>=) :: P a -> (a -> P b) -> P b
    (P a) >>= f = P (\st -> do (st', a') <- a st
			       let P b = f a'
			       b st')
			       
    fail str = P (\st -> if exitOnFail st 
			 then exit str
			 else let l = linenum st
				  c = colnum st
				  f = filename st
				  info = SrcInfo (-1) f l c (-1)
				  err  = mkError info str
			      in  simpleFailure [err])

-- runs parser on given string, returning:
--  - the next number in the fresh number store
--  - a list of source debugger commands
--  - the parse tree
runP :: String -> P a -> SimpleResult (Int, [SrcCommand], a)
runP str parser@(P a) = case a initState of
		Failure e b  -> Failure e b
		Success e (st, p) -> Success e (label st, commands st, p)
    where initState = MkState {input = str, prevInput = str,
			       noToken = True, layoutCols = [], 
			       indentToken = True,
			       exitOnFail = False, -- True,
			       linenum = 1, 
			       colnum = 1, tokCol = 1, tokRow = 1,
			       label = 0,
			       handleLayout = True,
			       tokensReady = False, 
			       prevToken = teof,
			       stream = [],
			       origStream = [],
			       commands = [],
			       filename = "",
			       modImportMode = False}

-- as above, but takes a filename and an initial value for label index
-- (also returns the remaining string input)
runPConf :: Filename -> UniqueNum -> String -> P a
         -> SimpleResult (String, [SrcCommand], Int, a, [AST.Token])
runPConf fn n s (P a) = case a initState of
		    Failure e b  -> Failure e b
		    Success e (st, p) -> let inp  = input st
					     cmds = commands st
					     ls   = label st
					     toks = map (AST.Token . fst3) 
							(origStream st)
					 in  Success e (inp, cmds, ls, p, toks)
    where initState = MkState {input = s, prevInput = s,
			       noToken = True, layoutCols = [],
			       indentToken = True,
			       exitOnFail = False, -- True,
			       linenum = 1, 
			       colnum = 1, tokCol = 1, tokRow = 1,
			       label = n,
			       handleLayout = True,
			       tokensReady = False, 
			       prevToken = teof,
			       stream = [], 
			       origStream = [],
			       commands = [],
			       filename = fn,
			       modImportMode = False}
runPConf_ = runPConf ""


-- returns row,column position of parser
--getPos :: P (Int, Int)
getPos = P (\st -> return (st, (filename st, linenum st, colnum st)))


getFileName = P (\st -> return (st, filename st))

getColNum :: P Col
getColNum = P (\st -> return (st, colnum st))

getLineNum :: P Row
getLineNum = P (\st -> return (st, linenum st))

incLineNum :: P ()
incLineNum = P (\st -> return (st{linenum = linenum st + 1}, ()))

setLineNum :: Row -> P ()
setLineNum r = P (\st -> return (st{linenum = r}, ()))

setColNum :: Col -> P ()
setColNum c = P (\st -> return (st{colnum = c}, ()))

incColNum :: P ()
incColNum = addColNum 1


addColNum :: Int -> P ()
addColNum n = P (\st -> return (st {colnum = colnum st + n}, ()))


resetColNum :: P ()
resetColNum = P (\st -> return (st {colnum = 1, noToken = True}, ()))

tabColNum :: P ()
tabColNum = P (\st -> return (st {colnum = tab (colnum st)}, () ))
    where tab n = ((n `div` 8) + 1) * 8 + 1


newLabel = P (\st -> return (st 
	{label = let n = label st in n+1}, label st))

{- --  TEST -- REMOVE!
newLabel = P (\st -> return (st 
	{label = let n = label st in n+1}, -1))
-}
 
getInput :: P String
getInput = P (\st -> return (st, input st))

getPrevInput :: P String
getPrevInput = P (\st -> return (st, prevInput st))



getTokCol :: P Col
getTokCol = P (\st -> return (st, tokCol st))

getTokRow :: P Row
getTokRow = P (\st -> return (st, tokRow st))

updateTokPos :: P ()
updateTokPos = P (\st -> return (st {tokCol = colnum st, 
				     tokRow = linenum st} ,()))

setInput :: String -> P ()
setInput s = P (\st -> return (st {prevInput = input st, input = s}, ()))

ckHandleLayout :: P Bool
ckHandleLayout = P (\st -> return (st, handleLayout st))

doHandleLayout :: P ()
doHandleLayout = P (\st -> return (st {handleLayout = True}, ()))

dontHandleLayout :: P ()
dontHandleLayout = P (\st -> return (st {handleLayout = False}, ()))

dontExitOnFail :: P ()
dontExitOnFail = P (\st -> return (st {exitOnFail = False}, ()))

useModImportMode :: P ()
useModImportMode = P (\st -> return (st {modImportMode = True}, ()))

ckModImportMode :: P Bool
ckModImportMode = P (\st -> return (st, modImportMode st))

---------------------------------------- 

-- use these functions to build tokens by introducing positional information
-- WARNING: these *MUST* be called after a token is recognised, but *BEFORE* the
--	    lexer's internal position state is updated! (a number of utility
--	    functions automatically update the internal state!)

mkPosToken :: (Src a -> Token) -> a -> P Token
mkPosToken tk a = getPos >>= \pos -> return (tk (a, pos))

mkStdPosToken :: (Src String -> Token) -> P Token
mkStdPosToken tk = getPos >>= \pos -> return (tk ("", pos))

----------------------------------------

-- given an AST node constructor, a token Src value, produces an appropriate
-- SrcInfo, and constructs the AST node
mkNode :: (SrcInfo -> a -> b) -> Src c -> a -> P b
mkNode f (_, (mod,row,col)) a = do
    n <- newLabel
    let s = SrcInfo { srcLoc = n, srcFile = mod, 
		      srcRow = row, srcCol = col, srcOffset = -98 }
    return (f s a)

mkNode0 :: (SrcInfo -> a) -> Src b -> P a
mkNode0 f (_, (mod, row,col)) = do
    n <- newLabel
    let s = SrcInfo { srcLoc = n, srcFile = mod, 
		      srcRow = row, srcCol = col, srcOffset = -98 }
    return (f s)


-- as above, but puts the result in a list
mkNodes :: (SrcInfo -> a -> b) -> Src c -> a -> P [b]
mkNodes f s a = mkNode f s a >>= \n -> return [n]

-- as per mkNode, but takes two arguments for the AST node constructor
mkNode2 :: (SrcInfo -> a -> b -> c) -> Src d -> a -> b -> P c
mkNode2 f (_, (mod,row,col)) a b = do
    n <- newLabel
    let s = SrcInfo { srcLoc = n, srcFile = mod, 
		      srcRow = row, srcCol = col, srcOffset = -98 }
    return (f s a b)

mkNode3 :: (SrcInfo -> a -> b -> c -> d) -> Src e -> a -> b -> c -> P d
mkNode3 f (_, (mod,row,col)) a b c = do
    n <- newLabel
    let s = SrcInfo { srcLoc = n, srcFile = mod, 
		      srcRow = row, srcCol = col, srcOffset = -98 }
    return (f s a b c)


-- same as mkNode, but takes an additional function (constructor) as its first 
-- argument which it applies to the result of the mkNode
mkNestedNode :: (b -> d) -> (SrcInfo -> a -> b) -> Src c -> a -> P d
mkNestedNode g f s a = mkNode f s a >>= \n -> return (g n)

-- it's starting to get convoluted now
mkNestedNode2 :: (b -> e -> d) -> (SrcInfo -> a -> b) -> Src c -> a -> e -> P d
mkNestedNode2 g f s a e = mkNode f s a >>= \n -> return (g n e)

-- see above
mkNestedNode3 :: (b -> e -> h -> d) -> (SrcInfo -> a -> b) -> Src c 
	      -> a -> e -> h -> P d
mkNestedNode3 g f s a e h = mkNode f s a >>= \n -> return (g n e h)

-- see above
mkNestedNode4 :: (b -> e -> h -> i -> d) -> (SrcInfo -> a -> b) -> Src c 
              -> a -> e -> h -> i -> P d
mkNestedNode4 g f s a e h i = mkNode f s a >>= \n -> return (g n e h i)
	      


-- extracts a Src structure from a node that already has a SrcInfo
extractSrc :: HasSrcInfo a => a -> Src String
extractSrc a = 
    let src = getSrcInfo a
	f = srcFile src
	r = srcRow src
	c = srcCol src
    in  ("", (srcFile src, srcRow src, srcCol src))

----------------------------------------
pushCol :: Int -> P ()
pushCol n = P (\st -> return (st {layoutCols = n : layoutCols st}, ()))

initLayoutCols :: Int -> P ()
initLayoutCols n = P (\st -> return (st {layoutCols = [n]}, ()))

emptyCols :: P Bool
emptyCols = P (\st -> return (st, null (layoutCols st)))

popCol :: P Int
popCol = topColF tl
	  
topCol :: P Int
topCol = topColF id

-- manipulate the stack, also return the top element
topColF :: ([Int] -> [Int]) -> P Int
topColF f = P (\st -> let cs = layoutCols st
		      in  return (st {layoutCols = f cs}, hd cs))
    where hd []	    = error "ParserMisc.popCol.hd"
	  hd (x:_)  = x


-- remove from the token stream the right brace which would match the last read
-- left brace (closing the block)
-- NOTE: we do this when accepting a parse error instead of a '}', since the
--	 layout-removal process will have placed the '}' in the wrong place
--	 anyway.
dropContextEnd :: P ()
dropContextEnd = do ts <- getStream
		    setStream (rem ts 0)
    where rem [] _ = []
	  rem (i@(TLBrace,_,_):is) c = i : rem is (c+1)
	  rem (i@(TRBrace,_,_):is) c = if c == 0 then is
						 else i : rem is (c-1)
	  rem (i@(t,_,_):is) c = i : rem is c
    

----------------------------------------

sawToken :: P ()
sawToken = setNoToken False

clrNoToken = sawToken

setNoToken :: Bool -> P ()
setNoToken b = P (\st -> return (st {noToken = b}, ()))

getNoToken :: P Bool
getNoToken = P (\st -> return (st, noToken st))

setIndentToken, clrIndentToken :: P ()
setIndentToken = P (\st -> return (st {indentToken = True}, ()))
clrIndentToken = P (\st -> return (st {indentToken = False}, ()))

wasIndentToken :: P Bool
wasIndentToken = P (\st -> return (st, indentToken st))


----------------------------------------

getState :: P State
getState = P (\st -> return (st, st))

setState :: State -> P ()
setState st = P (\_ -> return (st, ()))

----------------------------------------

tokensAvailable :: P Bool
tokensAvailable = P (\st -> return (st, tokensReady st))

tokensDone :: P ()
tokensDone = P (\st -> return (st {tokensReady = True}, ()))

getPrevToken :: P TokenInfo
getPrevToken = P (\st -> return (st, prevToken st))

setStream :: [TokenInfo] -> P ()
setStream ts = P (\st -> return (st {stream = ts}, ()))

getStream :: P [TokenInfo]
getStream = P (\st -> return (st, stream st))


setOrigStream :: [TokenInfo] -> P ()
setOrigStream ts = P (\st -> return (st {origStream = ts}, ()))

getOrigStream :: P [TokenInfo]
getOrigStream = P (\st -> return (st, origStream st))

popToken :: P TokenInfo
popToken = P (\st -> let ts = stream st
			 t  = headMsg "yo" ts
		     in  return (st {stream = tl ts, prevToken = t}, t))

pushToken :: TokenInfo -> P ()
pushToken t = P (\st -> return (st {stream = t:stream st}, ()))

tl [] = trace "EMPTY CONTEXT STACK" []
tl xs = tail xs
hd [] = error "ParserMisc.hd"
hd xs = head xs

-- also updates the parsers position state
nextToken :: P Token
nextToken = do (t,r,c) <- popToken
	       setLineNum r
	       setColNum c
	       return t

addCommand :: SrcCommand -> P ()
addCommand sc = P (\st -> return (st { commands = sc : commands st }, ()))

--------------------------------------------------------------------------------

-- This function removes all tokens not related to import declarations.
-- WARNING:
-- This step must be performed before before executing the module-import parser.
cleanupTokensImport :: [TokenInfo] -> [TokenInfo]
cleanupTokensImport = proc 1
  where
    -- a simple state machine, leaving behind only tokens forming a semicolon
    -- separated list of import declarations
    proc :: Int -> [TokenInfo] -> [TokenInfo]
    proc 1 (ti@(TLBrace,_,_):tis) = proc 2 tis
    -- proc 1 tis@((TImport _,_,_):_) = proc 2 tis
    proc 1 (ti:tis) = proc 1 tis

    proc 2 (ti@(TImport _,_,_):tis)  = ti : proc 3 tis
    proc 2 (ti:tis) = [teof] 

    proc 3 (ti@(TSemicolon,_,_):tis@((TImport _,_,_):_)) = ti : proc 2 tis
    proc 3 (ti@(TSemicolon,_,_):tis) = [teof]
    proc 3 (ti:tis) = ti : proc 3 tis

    proc _ [] = [teof]

--------------------------------------------------------------------------------


-- NOTE: use distinguishable types in these equations, types that the user
--	 can't specify (so that we can later identify them as originating from
--	 `True' and `False' terms.)
mkTrueEqPrim, mkFalseEqPrim :: Pred -> Prim
mkTrueEqPrim  (Pred s _ _) = let a = VarType (anonId "a!")
			     in  EqPrim s a a
mkFalseEqPrim (Pred s _ _) = let a   = VarType (anonId "a!")
				 app = AppType s a a
			     in  EqPrim s a app

isTruePred  (Pred _ id _) = idStr id == "True" 
isFalsePred (Pred _ id _) = idStr id == "False" 


----------------------------------------

-- takes a type of form (T t1 ... tn), and turns it into a 
-- predicate (P [t1, ..., tn]) - where the list type is unique to
-- multi-parameter type classes 
typeToPred :: Type -> P Pred
typeToPred t = do
    res@(id, ts) <- undo t []
    return (Pred (idSrcInfo id) id ts)
  where
	-- undoes nested applications
	undo :: Type -> [Type] -> P (Id, [Type])
	undo (AppType s t1 t2) as = case t1 of 
		AppType _ _ _ -> undo t1 (t2:as)
		ConType id  -> return (id, t2:as)
		-- if the left-most operator is a variable, its a parse error 
		-- (i.e. a variable can't have the same name as a type class)
		VarType id  -> let pos = formatSrcPos (idSrcInfo id) ++ 
					 "(FIXME:format this better)"
			       in  fail ("Parse error in type class at " ++ pos)
	undo t _ = fail ("Parse error: bad type class constraint: " ++ show t)


----------------------------------------

tupToCtxt :: Type -> P Ctxt
tupToCtxt t = do
    ps <- case t of
	    TupType _ ts  -> mapM cToPred ts
	    AppType _ b c -> typeToPred t >>= \p -> return [p]
	    _	-> fail "Parse error in context (1b) (FIXME: improve this msg)"
    return (Ctxt ps)
  where
    cToPred :: Type -> P Pred
    cToPred t = case t of
	AppType _ b c -> typeToPred t
	_   -> fail "Parse error in context (2b) (FIXME: improve this msg)"
	

addInfixParens :: Exp -> Exp
addInfixParens (IfxAppExp s e1 e2 e3) = PIfxAppExp s e1 e2 e3
addInfixParens e = e


-- converts an expression to a pattern, if possible
-- (in some cases e.g. list comprehensions, we parse patterns as expressions to
--  avoid ambiguity in the grammar)
expToPat :: Exp -> Pat
expToPat e = case e of
    VarExp id  -> VarPat id
    ConExp id  -> ConPat (getSrcInfo id) id []
    LitExp lit -> LitPat lit
    TupExp s es    -> TupPat s (map expToPat es)
    ListExp s (Many _ es) -> ListPat s (map expToPat es)
    AppExp s e1 e2 -> let (c:_, ps) = appToPat [] [] e
		      in  ConPat s c ps
    _ -> error ("malformed pattern: " ++ show e ++ "FIXME: improve msg")

  where
    appToPat c as e = case e of
	AppExp s e1 e2 -> let (c1, as1) = appToPat c as e1
			      (c2, as2) = appToPat c [] e2
			      as3 = case c2 of
				    []    -> as2
				    (c:_) -> [ConPat s c as2]
			  in  (c1, as1 ++ as3)

	ConExp id      -> (id:c, as)
	
	_	       -> (c, as ++ [expToPat e])


{-

----------------------------------------

--------------------------------------------------------------------------------

        


----------------------------------------

----------------------------------------

-- adds an undefined definition for the instance declaration given
-- (only if there are no existing definitions for that instance)
-- e.g.	    instance C a => C [a]
--
-- BECOMES  instance C a => C [a] where
--		c = undefined
addUndefinedInstanceDef :: Dec -> P Dec
addUndefinedInstanceDef dec = case dec of 
    InstDec asig [] -> case item asig of
	    InstSig ctxt (Ann x (Pred id t)) -> do
		x1 <- newLabel
		x2 <- newLabel
		x3 <- newLabel
		let rhs = Ann x1 (RHS1 (Ann x1 (VarExp "undefined")))
		    def = Def (Ann x2 (varId id)) [] rhs []
		    adef= Ann x3 def
		return (InstDec asig [adef])
    _ -> return dec

addUndefinedOverloadDef :: Dec -> P Dec
addUndefinedOverloadDef dec = case dec of 
    OverDec asig [] -> case item asig of
	    Sig at aid ctxt t -> do
		x1 <- newLabel
		x2 <- newLabel
		x3 <- newLabel
		let id  = item aid 
		    rhs = Ann x1 (RHS1 (Ann x1 (VarExp "undefined")))
		    def = Def (Ann x2 id) [] rhs []
		    adef= Ann x3 def
		return (OverDec asig [adef])
    _ -> return dec


--------------------------------------------------------------------------------


--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-}


-- an end-of-file token
teof = (Teof, -1, -1)

