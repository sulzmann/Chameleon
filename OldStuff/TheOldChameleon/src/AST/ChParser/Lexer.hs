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
-- | Lexer for Chameleon.
--
--------------------------------------------------------------------------------

module AST.ChParser.Lexer (
    lexer, Token(..)
)
where

import AST.ChParser.ParserMisc
import AST.ChParser.Tokens
import Misc
import Misc.ErrorMsg

import Char
import Maybe
-- import IOExts

--------------------------------------------------------------------------------

-- | A two-stage lexer. The first time it's invoked, it does *all* the lexing,
-- layout transformation etc. Every subsequent invocation just returns the
-- next token in the already-available token stream. Kind of a hack.
-- NOTE: These two stages ought to be separated out. There's no need to
--	 perform this conditional test every time.
lexer :: (Token -> P a) -> P a
lexer cont = do 
    done <- tokensAvailable
    if done then do token <- nextToken
		    cont token
      else do -- the actual work
	input <- getInput
	ts  <- lexAll input
	pos@(_,r,c) <- getPos		    -- the end position
	lay <- ckHandleLayout
	mim <- ckModImportMode
	let tend = (Tend ((),pos),r,c)	    -- an end token
	
	    ts1 = if lay then transformLayout ts
			 else ts
	    ts2 | mim = cleanupTokensImport ts1
		| otherwise = ts1
	    ts3 = ts2 ++ [tend]
	    ts4 = trace ("layout-free token stream:\n" ++ showlist ts3) ts3
	setStream ts3
	setOrigStream ts3
	tokensDone
	lexer cont

--------------------------------------------------------------------------------

-- turn a stream of characters into a stream of tokens
lexAll :: String -> P [TokenInfo]
lexAll input = do setInput input
		  lex
    where lex = do input <- getInput
		   token <- lexer' input
		   row	 <- getTokRow
		   col   <- getTokCol
		   updateTokPos
		   let tinfo = (token, row, col)
		   if token == Teof then return [tinfo]
				    else do tokens <- lex
					    return (tinfo:tokens)

lexer' :: String -> P Token
lexer' "" = returnPI 0 Teof ""

-- char. literal
lexer' ('\'':xs) = do (c, len, rst) <- getCharLit xs
		      tk <- mkPosToken TChar c
		      addColNum (len + 1)
		      returnPI 0 tk rst

-- string literal
lexer' ('"':xs) = do (str, rst) <- getStrLit xs
		     tk <- mkPosToken TStr str
		     addColNum (length str + 1)
		     returnPI 1 tk rst

-- comment to the end of the line
lexer' ('-':'-':xs) = do xs' <- dropLine xs
			 lexer' xs'
			 
-- start of block comment
lexer' ('{':'-':xs) = do pos <- getPos
			 addColNum 2
			 dropBlock pos 1 xs
	                 s <- getInput
	                 lexer' s

lexer' xxs@(x:xs)
      -- skip whitespace
    | isSpace x = do xs' <- skipSpace xxs
		     setInput xs'
		     lexer' xs'

      -- some infixified function
    | x == '`' = do pos <- getPos 
		    m <- takeInfixNonSymbol xxs
		    let (str, rst) = fromJust m
		    if isNothing m 
		     then fail ("Badly formed operator at " ++ show pos ++
				" - no closing '")
		     else returnPI 0 (TIId (str, pos)) rst

    | isSymbol x = do pos <- getPos
		      (sym, rst) <- takeToken isSymbol xxs
		      let ms  = [ tok | (str,tok) <- keySymbols, sym == str ]
			  tok = case ms of
				-- an exact match (it's a known key symbol)
				(t:_) -> t (sym, pos)
				-- no exact match (it's an identifier)
				[]    -> TIId (sym, pos)
		      returnPI 0 tok rst
    
    | isPunct x  = do pos <- getPos
                      (pun, rst) <- takeToken isPunct xxs
                      let ms = prefixKeySymbol pun 
		      case ms of
                        -- it's a prefix of a known key symbol
                        ((t,(s,r)):_) -> let rst' = r ++ rst
					     tok  = t (s,pos)
					     ofs  = -(length r)
					 in  returnPI ofs tok rst'
                        
			-- no match (an invalid token!)
			[]    -> fail ("unrecognised token `" ++ pun ++ "'")

    | isAlphaChar x = 
		  do pos <- getPos
		     (str,ftok,rst) <- takeId xxs
		     case lookup str keywords of
			Nothing  -> returnPI 0 (ftok (str,pos)) rst
			Just tok -> returnPI 0 (tok ("",pos)) rst

    -- a numeric literal - int or float
    | isDigit x	= do (t, rst) <- getNumLit xxs
		     returnPI 0 t rst


    | otherwise		= fail ("unrecognised token `" ++ 
				    takeWhile (/='\n') xxs ++ "'")


-- standard symbols (NOTE: arranged by length of string)
keySymbols :: [(String, Src String -> Token)]
keySymbols = [	("<==>", TSimpArrow),	("==>", TPropArrow),
		("<=>", TSimpArrow), -- for all the CHR programmers out there
		(":::", TEAnn),		("::?", TQuery),
		("=>", TImpl),		("<-", TLArrow),
		("->", TArrow),		("..", TCont),
		("::", TAnn),           ("@_", TFunc),          
                ("*", TAsterisk),       --("-", TMinus),
		("?", TQuestion),       -- (":*:", TRAnn),
		("=", TEquals),		("\\", TBackslash), 
		("(", TLParen),		(")", TRParen),
		("[", TLBracket),	("]", TRBracket),
		(",", const TComma),	("@", TAt),
		("|", TBar),		("{", const TLBrace),
		("}", const TRBrace),	(";", const TSemicolon) ]


-- map from keyword strings to tokens
keywords :: [(String, Src String -> Token)]
keywords = [("rule", TRule), ("overload", TOverload), ("data", TData), 
	    ("class", TClass), ("instance", TInstance), 
	    ("deriving", TDeriving), ("hiding", THiding), 
	    ("primitive", TPrimitive),
	    ("infix", TInfix), ("infixl", TInfixl), ("infixr", TInfixr),
	    ("if", TIf), ("then", TThen), ("else", TElse), 
	    ("let", TLet), ("in", TIn), ("where", TWhere),
	    ("case", TCase), ("of", TOf), ("do", TDo), ("type", TType),
	    ("extern", TExtern), ("module", TModule), ("xmodule", TXModule), ("import", TImport),
	    ("as", TAs), ("qualified", TQualified), ("forall", TForall),
	    ("True", TTrue), ("False", TFalse), ("constraint", TConstraint)]

-- escapable chars
escapableChars = [('n','\n')]

-- keywords that introduce an indented scope
isIndentToken :: Token -> Bool
isIndentToken t = case t of
    TLet _ -> True
    TWhere _ -> True
    TOf _ -> True
    TDo _ -> True
    _ -> False


-- if some prefix of the given string is a key symbol, return the token it
-- represents, and a pair containing the matched prefix and the rest of the 
-- string (for all key symbols, in order of length of symbol - use head)
-- note that the "token" may need to be applied to a source position!
prefixKeySymbol :: String -> [(Src String -> Token, (String, String))]
prefixKeySymbol str = [ (t,(s,r)) | (s,t) <- keySymbols, 
				    let m = s `pre` str,	
				    isJust m, 
				    let r = fromJust m ]
    where   pre []     ys = Just ys
	    pre (x:xs) (y:ys) | x == y	= pre xs ys
	    pre _ _ = Nothing


-- skips over whitespace, incrementing position counters
skipSpace :: String -> P String
skipSpace "" = updateTokPos >> return ""
skipSpace (' ':xs)  = incColNum >> skipSpace xs
skipSpace ('\n':xs) = nextLinePos >> skipSpace xs
skipSpace ('\f':xs) = nextLinePos >> skipSpace xs
skipSpace ('\r':xs) = nextLinePos >> skipSpace xs
skipSpace ('\t':xs) = tabColNum >> skipSpace xs
skipSpace xs = updateTokPos >> return xs
    

nextLinePos = resetColNum >> incLineNum >> updateTokPos

-- returns prefix of string which satisfies the pred, as well as the rest
-- NOTE: do not use this to skip over whitespace! (it won't account for 
--	 newlines properly)
takeToken :: (Char -> Bool) -> String -> P (String, String)
takeToken _ ""    = return ("", "")
takeToken p xxs@(x:xs) = if p x then do (ts, rs) <- takeToken p xs
					incColNum
					return (x:ts, rs)
				else return ("", xxs)

-- reads a (possibly qualified) identifer name, returning the string name, the
-- constructor to build a token, and the rest of the string
takeId :: String -> P (String, Src String -> Token, String)
takeId xxs@(x:xs) = do 
    let (id,rs,isVarId) = takeQ xxs ""
	con | isVarId   = TId 
	    | otherwise = TConId
    addColNum (length id)
    return (id,con,rs)
  where

    takeQ :: String -> String -> (String,String,Bool)
    takeQ xxs@(x:_) id | isSmall x = let (l,rst) = span isIdChar xxs
				     in  (id++l,rst,True)
    takeQ xxs@(x:_) id | isUpper x = 
	let (u,rst) = span isIdChar xxs
	in  case rst of
		('.':rst'@(y:_)) | (isIdAlpha y || isSymbol y) -> takeQ rst' (id++u++".")
		rst' -> (id++u,rst,False)

    -- This handles function ids made up of symbols. Eg. &&, /=, ==, etc...
    takeQ xxs@(x:_) id | isSymbol x = 
        let (u,rst) = span isSymbol xxs 
        in (id++u,rst,True)

    -- NOTE: this state is unreachable (well, assuming no bugs)
    takeQ xs id = bug ("takeId unmatched, id: "++ show id ++ " xs: " ++ show xs)

    isIdAlpha c = isAlpha c || c == '\'' || c == '_'
    isIdChar  c = isAlphaNum c || c == '\'' || c == '_'
    isSmall   c = isLower c || c == '_'

-- takes a variable which has been applied infix (eg. `mod`)
takeInfixNonSymbol :: String -> P (Maybe (String, String))
takeInfixNonSymbol ('`':xs) = do 
    (str, rst) <- takeToken isIdChar xs
    case rst of 
	('`':rst') -> addColNum 2 >> return (Just (str, rst'))
	_	   -> return Nothing
takeInfixNonSymbol _ = return Nothing

isIdChar x = isAlphaNum x || x == '\'' || x == '_'
isLowerChar c = Char.isLower c || c == '_'
isAlphaChar c = Char.isAlpha c || c == '_'

-- True if the given character can appear within an operator name
isSymbol :: Char -> Bool
isSymbol c = c `elem` cs    where cs = ":!#$%&*+./<=>?@\\^|-~"

-- True if the given char appears within a key symbol (punctuation)
isPunct :: Char -> Bool
isPunct c = c `elem` cs	    where cs = "?(){}:;,.=<->|[]*\\"

-- assumes the given string begins a string literal
-- returns the literal, and the following list of chars
getStrLit :: String -> P (String, String)
getStrLit ('\\':'"':cs) = getStrLit cs >>= \(s, r) -> return ('\\':'"':s, r)
getStrLit ('"':cs)	= return ("", cs)
getStrLit (c:cs)	= getStrLit cs >>= \(s, r) -> return (c:s, r)
getStrLit ""		= fail "non-terminated string literal" 

-- assumes the given string begins a char literal
-- returns the literal, and the following list of chars
-- length returned is the length of the entire string literal, apart from the
-- leading open quote character (which is already accounted for by the caller.)
getCharLit :: String -> P (Char, Int, String)
getCharLit str = do (c, rst) <- get str
		    case c of
			[k] -> return (k, 2, rst)
			ks  -> case lookup ks val of
				Nothing -> fail ("unrecognised character " ++
						 "literal `" ++ ks ++ "'")
				Just k  -> return (k, length ks, rst)
		     
  where
    get ('\\':'\'':cs) = get cs >>= \(s, r) -> return ('\\':'"':s, r)
    get ('\'':cs)      = return ("", cs)
    get (c:cs)	       = get cs >>= \(s, r) -> return (c:s, r)
    get ""	       = fail "non-terminated string literal" 

    val = [("\\a",'\a'),("\\b",'\b'),("\\f",'\f'),("\\n",'\n'),("\\r",'\r'),
	   ("\\t",'\t'),("\\v",'\v'),("\\\\",'\\'),("\\\"",'"'),("\\'",'\'')]
    


-- reads the next number - int or float
-- also returns the remainder of the string
getNumLit :: String -> P (Token, String)
getNumLit ('0':b:cs) 
    | b == 'x' || b == 'X' = do let (num, rst) = span isHexDigit cs
				    hex = '0':b:num
				tk <- mkPosToken TInt (read hex, hex)
			        addColNum (length hex)
				return (tk, rst)

    | b == 'o' || b == 'O' = do let (num, rst) = span isOctDigit cs
				    oct = '0':b:num
				tk <- mkPosToken TInt (read oct, oct)
			        addColNum (length oct)
				return (tk, rst)
getNumLit cs = 
    case getDecimal cs of
	 (dec1, rst@('.':cs0)) -> -- float
		case getDecimal cs0 of
		 ([], cs0) -> -- no number after the decimal point, it's an int
			      do tk <- mkPosToken TInt (read dec1, dec1)
				 addColNum (length dec1)
				 return (tk, rst)
			     
		 (dec2, e:cs1)  
		    | e == 'e' || e == 'E' -> case cs1 of
			(s:cs2) | s == '+' || s == '-' -> do
			      let (dec3, cs3) = getDecimal cs2
				  f = dec1 ++ "." ++ dec2 ++ [e] ++ [s] ++ dec3
				  n = read (dec1 ++ dec2)
				  d = 10 ^ length dec2
				  nd | s == '+'  = (n * 10^(read dec3), d)
				     | otherwise = (n, d * 10^(read dec3))
				  
			      tk <- mkPosToken TFloat (read f, f, nd)
			      addColNum (length f)
			      return (tk, cs3)

			cs2 -> do let (dec3, cs3) = getDecimal cs2
				      f = dec1 ++ "." ++ dec2 ++ [e] ++ dec3
				      n = read (dec1 ++ dec2)
				      d = 10 ^ length dec2
				      nd = (n * 10^(read dec3), d)

				  tk <- mkPosToken TFloat (read f, f, nd)
				  addColNum (length f)
				  return (tk, cs3)

		 (dec2, cs1) -> do let f = dec1 ++ "." ++ dec2
				       n = read (dec1 ++ dec2)
				       d = 10 ^ length dec2
				       nd = (n,d)

				   tk <- mkPosToken TFloat (read f, f, nd)
				   addColNum (length f)
				   return (tk, cs1)
		      
	 (dec, cs0) -> -- decimal
		       do tk <- mkPosToken TInt (read dec, dec)
			  addColNum (length dec)
			  return (tk, cs0)
	 
    where getDecimal = span isDigit 



-- throws away the rest of the line (including the newline character)
dropLine :: String -> P String
dropLine "" = return ""
dropLine ('\n':xs) = nextLinePos >> return xs
dropLine (x:xs)	   = incColNum >> dropLine xs

-- discards characters from the given string until we leave the outer-most
-- comment block
-- dropBlock :: Int -> [Char] -> P ()
dropBlock pos n xs = db n xs
  where
    db 1 ('-':'}':xs) = addColNum 2 >> setInput xs
    db n ('-':'}':xs) = addColNum 2 >> db (n-1) xs
    db n ('{':'-':xs) = addColNum 2 >> db (n+1) xs
    db n ('\n':xs)    = do incLineNum
			   resetColNum
			   db n xs
    db n (_:xs) = incColNum >> db n xs
    db _ [] = fail $ "comment started at " ++ formatSrcPosVerbose pos ++ 
		     ", not closed by end of file"


-- Like return, but update the pending input stream as well.
-- Also increments the column number by the given ammount
returnPI :: Int -> Token -> String -> P Token
returnPI n t s = do addColNum n
		    setInput s
		    return t


--------------------------------------------------------------------------------
-- deal with layout
-- NOTE: this procedure is largely lifted from the Haskell 98 Report (Sec 9.3)

transformLayout :: [TokenInfo] -> [TokenInfo]
-- transformLayout = removeLayout . addLayoutTokens
transformLayout ts = let tsx  = addLayoutTokens ts
			 tsx' = removeLayout tsx
		     in  -- trace ("token stream with layout tokens:\n" ++	showlist tsx ++ "\nlayout-insensitive token stream:\n" ++ showlist tsx')  
				tsx'

-- transforms a Chameleon program into an equivalent layout-insensitive version
removeLayout :: [TokenInfo] -> [TokenInfo]
removeLayout ts = lay (init ts) [] ++ [teof]

    where
    
    lay tts@((TLayoutFirst n,r,c):ts) mms@(m:ms) 
	| m == n    = sc r c : lay ts mms
	| n <  m    = rb r c : lay tts ms

    lay tts@((TLayoutFirst n,r,c):ts) ms = lay ts ms


    lay ((TLayoutBlock n,r,c):ts) mms@(m:ms) 
	| n > m	    = lb r c : lay ts (n:mms)

    lay ((TLayoutBlock n,r,c):ts) [] 
	| n > 0	    = lb r c : lay ts [n]

    lay ((TLayoutBlock n,r,c):ts) ms = lb r c : rb r c : 
				       lay ((TLayoutFirst n,r,c):ts) ms

    lay ((TRBrace,r,c):ts) (0:ms) = rb r c : lay ts ms

    lay ((TRBrace,r,c):ts) ms = exit "removeLayout: parse error 1"

    lay ((TLBrace,r,c):ts) ms = lb r c : lay ts (0:ms)

    -- missing the case where we insert '}' in the event of a parse error

    lay [] [] = []
  
    lay [] (m:ms) 
	| m /= 0    = rb' m : lay [] ms
	| otherwise = exit (errorMsgNoSrc ["Parse error, outer-most \
					    \declaration block not closed",
					   "(try adding a '}' to the end)"])

    lay (t:ts) ms = t : lay ts ms


    rb' m = (TRBrace, -1, m)
    sc r c = (TSemicolon, r, c)
    lb r c = (TLBrace, r, c)
    rb r c = (TRBrace, r, c)


-- adds layout tokens to the token stream
addLayoutTokens :: [TokenInfo] -> [TokenInfo]
addLayoutTokens ts = let ts' = init (first ts)
		     in  add ts' ++ [teof]
    where

    -- if the program doesn't start with a '{' or `module' or `xmodule', note the 
    -- indentation of the first token
    first tts@((t,r,c):_) = case t of
	TLBrace -> tts
	TModule _ -> tts
        TXModule _ -> tts 
	_ -> (TLayoutBlock c, r, c) : tts

    add :: [TokenInfo] -> [TokenInfo]
    add [x@(t,r,c)]
	-- token introduces a new block, but is not followed by anything
	| isIndentToken t = x : [(TLayoutBlock 0, r, c)]
	| otherwise	  = [x]
	
    add (x1@(t1,r1,c1):x2@(t2,r2,c2):ts)
	-- token t1 introduces a new block
	| isIndentToken t1 && t2 /= TLBrace = 
			x1 : (TLayoutBlock c2,r2,c2) : add (x2:ts)
	-- check if t2 is first on its line
	| r2 > r1   = x1 : (TLayoutFirst c2, r2, c2) : add (x2:ts)
	| otherwise = x1 : add (x2:ts)




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- OLD

{-
    | isPunct x || isSymbol x = 
		  do pos <- getPos
		     st  <- getState	-- kinda hacky
		     (pstr, prst) <- takeToken isPunct xxs
		     (sstr, srst) <- takeToken isSymbol xxs
		     setState st
		     let m = prefixKeySymbol pstr
			 (tk,(s,r)) = head m
		     if null m || length sstr > length s
		      then -- handle unimary minus as a separate kind of token
			   case sstr of
--			    "-" -> do takeToken isSymbol xxs
--				      returnPI 0 (TMinus pos) srst
			    _   -> do takeToken isSymbol xxs
				      returnPI 0 (TIId (sstr, pos)) srst
		      else do takeToken isPunct xxs
			      -- let t = either id ($pos) et
			      let t = tk (s,pos)
			      returnPI (-(length r)) t (r ++ prst)
-}
