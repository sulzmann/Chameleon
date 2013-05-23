--------------------------------------------------------------------------------
--
-- The Scheme Back-end.
--
--------------------------------------------------------------------------------

module Backends.Scheme.GenerateStrict (
    generate
) where

import qualified AST.Internal as AI
import Backends.Internal as BI
import Backends.Scheme.AST as BSA
import Backends.Scheme.IdentTrans as IT

import Backends.Scheme.RFC2279 as UTF8

--------------------------------------------------------------------------------

-- Translates a program in the internal syntax into a String representing a
-- Scheme source file.
generate :: AI.Prog -> String
generate = prettyPrint . trProg . pProg

----------------------------------------

-- notes
-- 1. represent a character by its UTF8 encoding in a Scheme string
-- 2. represent a list by nested cons cells (a proper Scheme list)
-- 3. represent an element of an algebraic data type by a vector;
-- constructorname is taken over, 
-- selector names are constructorname.i for the i-th component

-- questions
-- 1. what happens to record operations?

trProg :: Prog -> Program
trProg (Prog mods) = Program $ map trModule mods

trModule :: Module -> CommandOrDefinition
trModule mod =
  let decs = moduleDecs mod 
      sc_decs = map trDec decs
  in
  case sc_decs of
    [justOneDec] -> justOneDec
    cods -> CODBegin cods

trDec :: Dec -> CommandOrDefinition
trDec (ValDec _ lb) = 
  CODDefinition (trLetBnd lb)
trDec (DataDec _ dt css) =
  CODBegin (trDataDec dt css)

trDataDec :: AI.DataType -> [Cons] -> [CommandOrDefinition]
trDataDec _ css =
  zipWith trCons [0..] css

trCons :: Integer -> Cons -> CommandOrDefinition
trCons ctor (Cons _ dt) =
  CODDefinition (trDataType ctor dt)

trDataType :: Integer -> AI.DataType -> Definition
trDataType ctor (AI.DataType id tys) = 
  let basename = IT.f id
      SId basestr = basename
      mkSelector ty i =
	let suffix = '.' : show i in
	DefFunction (SId (basestr ++ suffix))
		    (DefFormals [SId "x"])
		    (Body []
		     (Sequence
		      [ProcedureCall (Variable (SId "vector-ref"))
				     [Variable (SId "x")
				     ,Literal (LitNumber (NumInteger (i+1)))]]))
      mkConstructor [] _ =
	ProcedureCall (Variable (SId "vector")) 
		      (Literal (LitNumber (NumInteger ctor))
		      :
		      zipWith (\_ i -> Variable (SId ('x' : show i))) tys [0..])
      mkConstructor (ty : tys) (i : is) =
	lambda [SId ('x' : show i)] (mkConstructor tys is)
  in
  DefBegin 
  ( -- the constructor function (external use, must be curried!)
  DefSingle basename (mkConstructor tys [0..])
  : -- the test function (internal use)
  DefFunction (SId ('?' : basestr))
	      (DefFormals [SId "x"])
	      (Body []
	       (Sequence
		[ProcedureCall 
		 (Variable (SId "equal?"))
		 [Literal (LitNumber (NumInteger ctor))
		 ,ProcedureCall 
		  (Variable (SId "vector-ref"))
		  [Variable (SId "x")
		  ,Literal (LitNumber (NumInteger 0))]]]))
  : -- the selector functions (internal use)
  zipWith mkSelector tys [0..])
  

trLetBnd :: LetBnd -> Definition
trLetBnd (LetBnd _ id exp) = 
  DefSingle (IT.f id)
	    (trExp exp)

trExp :: BI.Exp -> BSA.Exp
trExp (BI.VarExp id) = Variable (IT.f id)
trExp (BI.ConExp id) = Variable (IT.f id)
trExp (BI.LitExp lit) = Literal (trLit lit)
trExp (BI.AppExp si e1 e2) = ProcedureCall (trExp e1) [trExp e2]
trExp (BI.AbsExp si id exp) = LambdaExpression (Formals [IT.f id]) 
					       (Body []
						(Sequence [trExp exp]))
trExp (BI.LetExp si lbs exp) = ProcedureCall (LambdaExpression (Formals [])
					      (Body (map trLetBnd lbs)
					       (Sequence [trExp exp])))
					     []
trExp (BI.CaseExp si es ms) =
      let names = zipWith g es [0..] 
	  g e i = SId ('x' : show i)
      in
      ProcedureCall (LambdaExpression 
		     (Formals names)
		     (Body [] 
		      (Sequence 
		       [ProcedureCall (Variable (SId "call-with-current-continuation"))
				      [LambdaExpression 
				       (Formals [SId "ret"])
				       (Body []
				       (Sequence (trMatches names ms)))]])))
		    (map trExp es)

-- Compilation of pattern matching
-- (call/cc \ return ->
--   (call/cc \ fail ->
--     (return (check-match-with-exit fail match1)))
--   (call/cc \ fail ->
--     (return (check-match-with-exit fail match2)))
--   (display "match failed")
--   (error))
trMatches :: [SId] -> [BI.Match] -> [BSA.Exp]
trMatches names [] = 
  [ProcedureCall (Variable (SId "display"))
		 [Literal (LitString "match failed")]
  ,ProcedureCall (Variable (SId "/"))
		 [Literal (LitNumber (NumInteger 1))
		 ,Literal (LitNumber (NumInteger 0))]
  ]
trMatches names (Match ps e: ms) =
  ProcedureCall
    (Variable (SId "call-with-current-continuation"))
    [LambdaExpression 
     (Formals [SId "fail"])
     (Body []
      (Sequence [ProcedureCall 
		 (Variable (SId "ret"))
		 [trMatch names ps e]]))]
  :
  trMatches names ms

trMatch :: [SId] -> [AI.Pat] -> BI.Exp -> BSA.Exp
trMatch [] [] e = trExp e
trMatch (id : ids) (p : ps) e =
  case p of
    AI.VarPat vid ->
      ProcedureCall 
	(lambda 
	 [IT.f vid]
	 (trMatch ids ps e))
	[Variable id]
    AI.LitPat lit ->
      Conditional
	(ProcedureCall
	 (Variable (SId "equal?"))
	 [Variable id, Literal (trLit lit)])
	(trMatch ids ps e)
	(Just (ProcedureCall
	       (Variable (SId "fail"))
	       []))
    AI.ConPat si cid cps ->
      let SId basestr = id
	  SId cbasestr = IT.f cid
	  ctortest = SId ('?' : cbasestr)
	  csubids = zipWith g cps [0..]
	  g _ i = SId (basestr ++ '.' : show i)
      in
      Conditional
	(ProcedureCall
	 (Variable ctortest)
	 [Variable id])
	(ProcedureCall 
	 (lambda csubids 
	  (trMatch (csubids ++ ids) (cps ++ ps) e))
	 (zipWith (callCtorSelector cbasestr id) cps [0..]))
	(Just (ProcedureCall
	       (Variable (SId "fail"))
	       []))

callCtorSelector :: String -> SId -> a -> Integer -> BSA.Exp
callCtorSelector cbasestr id _subpattern ctor =
  ProcedureCall 
    (Variable (SId (cbasestr ++ '.' : show ctor)))
    [Variable id]
      
trLit :: AI.Lit -> Literal
trLit (AI.IntegerLit si i str) = LitNumber (NumInteger i)
trLit (AI.IntLit si i) = LitNumber (NumInteger (fromIntegral i))
trLit (AI.FloatLit si d r str) = LitNumber (NumDouble d)
trLit (AI.StrLit si str) = LitQuotation (trStrLit str)
trLit (AI.CharLit si c) = LitString (UTF8.encode [c])

trStrLit :: String -> Datum
trStrLit str = DatList (map trStrChar str)

trStrChar :: Char -> Datum
trStrChar c = DatString (UTF8.encode [c])

