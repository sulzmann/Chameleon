module Backends.Scheme.AST where

import Char

import Text.PrettyPrint.HughesPJ

import AST.Common

--------------------------------------------------------------------------------

data SId =			    -- Scheme identifier
    SId String

data Exp
  = Variable SId
  | Literal Literal
  | ProcedureCall Exp [Exp]
  | LambdaExpression Formals Body
  | Conditional Exp Exp (Maybe Exp)
  | Assignment SId Exp
--  | MacroUse Keyword [Datum]
--  | MacroBlock -- (let-syntax ...)
  -- and some derived ones
  | Begin [Exp]
    
data Literal 
  = LitQuotation Datum
  | LitBoolean Bool
  | LitNumber Number
  | LitCharacter Char
  | LitString String

data Datum
  = DatBoolean Bool
  | DatNumber Number
  | DatCharacter Char
  | DatString String
  | DatSymbol SId		    -- ^ String must be valid Scheme symbol
  | DatList [Datum]
  | DatImproperList [Datum] Datum Datum
  | DatVector [Datum]

data Number
  = NumInteger Integer
  | NumDouble Double

data Body
  = Body [Definition] Sequence

data Sequence
  = Sequence [Exp]

-- all string args must be valid Scheme identifiers
data Formals
  = Formals [SId]
  | OneFormal SId
  | ImproperFormals [SId] SId SId

data Definition
  = DefSingle SId Exp
  | DefFunction SId DefFormals Body
  | DefBegin [Definition]

data DefFormals
  = DefFormals [SId]
  | DefImproperFormals [SId] SId

data CommandOrDefinition
  = CODCommand Exp
  | CODDefinition Definition
  -- syntax definition
  | CODBegin [CommandOrDefinition]

data Program
  = Program [CommandOrDefinition]

-- convenience functions
lambda :: [SId] -> Exp -> Exp
lambda ids exp =
  LambdaExpression 
    (Formals ids)
    (Body [] (Sequence [exp]))

-- serialization as a Scheme program
class Serialize a where
  serialize :: a -> Doc

instance Serialize SId where
  serialize (SId s) = text s

instance Serialize Exp where
  serialize e =
    case e of
      Variable id -> serialize id
      Literal lit -> serialize lit
      ProcedureCall e es ->
	parens (serialize e $$ nest 1 (sep (map serialize es)))
      LambdaExpression formals body ->
	parens (text "lambda" <+> serialize formals $$
		nest 1 (serialize body))
      Conditional e1 e2 Nothing ->
	parens (text "if" <+> vcat [serialize e1, serialize e2])
      Conditional e1 e2 (Just e3) ->
	parens (text "if" <+> vcat [serialize e1, serialize e2, serialize e3])
      Assignment id e1 ->
	parens (text "set!" <+> serialize id <+> serialize e1)
      Begin es ->
	parens (text "begin" $$ nest 2 (vcat (map serialize es)))

instance Serialize Literal where
  serialize lit =
    case lit of
      LitQuotation datum ->
	parens (text "quote" <+> serialize datum)
      LitBoolean bool ->
	serialize bool
      LitNumber num ->
	serialize num
      LitCharacter c ->
	serialize c
      LitString s ->
	ppString s

ppString s = doubleQuotes (hcat (map ppStringChar s))

ppStringChar c =
  let oc = ord c 
      (ocDiv8,  digit0) = oc `divMod` 8
      (ocDiv64, digit1) = ocDiv8 `divMod` 8
      (ocDiv512, digit2) = ocDiv64 `divMod` 8
      o0 = ord '0'
  in
  if oc < 256
  then char '\\' 
    <> char (chr (digit2 + o0))
    <> char (chr (digit1 + o0))
    <> char (chr (digit0 + o0))
  else error ("ppStringChar: character out of range "++ show c)

instance Serialize Char where
  serialize ch =
    if ch < chr 256
    then text "#\\" <> char ch
    else error ("serialize[Char]: character out of range "++ show ch)

instance Serialize Bool where
  serialize True  = text "#t"
  serialize False = text "#f"

instance Serialize Number where
  serialize (NumInteger i) = integer i
  serialize (NumDouble d)  = double d
  -- Scheme reads this value with default precision (whatever that is)
  -- to obtain more control over precision, we would have to change the 
  -- 'e' for the exponent to 'd' for double precision
  -- the following letters are available: s, f, d, l
  -- R5RS, 6.2.4, p21

instance Serialize Datum where
  serialize (DatBoolean b) = serialize b
  serialize (DatNumber n) = serialize n
  serialize (DatCharacter c) = serialize c
  serialize (DatString s) = ppString s
  serialize (DatSymbol id) = serialize id
  serialize (DatList ds) = parens (sep (map serialize ds))
  serialize (DatImproperList ds dx dy) = 
	    parens (sep (map serialize ds) 
		    <+> serialize dx
		    <+> char '.'
		    <+> serialize dy)
  serialize (DatVector ds) = char '#' <> parens (sep (map serialize ds))

instance Serialize Body where
  serialize (Body defs seq) =
    vcat (map serialize defs)
    $$ serialize seq

instance Serialize Sequence where
  serialize (Sequence exps) =
    vcat (map serialize exps)

instance Serialize Formals where
  serialize (Formals ids) = parens (sep (map serialize ids))
  serialize (OneFormal id) = serialize id
  serialize (ImproperFormals ids idx idy) = parens (sep (map serialize ids) 
						   <+> serialize idx
						   <+> char '.'
						   <+> serialize idy)

instance Serialize Definition where
  serialize (DefSingle id exp) =
	    (lparen <> text "define" <+> serialize id) $$
	    nest 2 (serialize exp <> rparen)
  serialize (DefFunction id fs body) =
	    (lparen <> text "define" <+>
	               parens (serialize id <+> serialize fs)) $$
	    nest 2 (serialize body <> rparen)
  serialize (DefBegin defs) =
	    (lparen <> text "begin") $$ nest 2 (vcat (map serialize defs) <> rparen)
instance Serialize DefFormals where
  serialize (DefFormals ids) = sep (map serialize ids)
  serialize (DefImproperFormals ids id) = sep (map serialize ids)
	                                  <+> char '.'
					  <+> serialize id

instance Serialize CommandOrDefinition where
  serialize (CODCommand e) = serialize e
  serialize (CODDefinition d) = serialize d
  serialize (CODBegin cods) =
	    (lparen <> text "begin") $$ nest 2 (vcat (map serialize cods) <> rparen)

instance Serialize Program where
  serialize (Program cods) =
	    vcat (map serialize cods)

prettyPrint :: Serialize a => a -> String
prettyPrint = render . serialize
