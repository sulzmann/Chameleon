--------------------------------------------------------------------------------
--
-- The LVM Back-end.
--
--------------------------------------------------------------------------------

module Backends.Lvm.ToLvmCore (
    toLvmCore 
) where

import qualified AST.Internal as AI
import Backends.Internal as BI
import Backends.Lvm.CoreAST as Core
   ( Module (..)
   , Decl (..)
   , DeclKind (..)
   , Custom (..)
   , Id
   , CoreModule
   , CoreDecl
   , Access (..)
   , Expr(..)
   , Note(..)
   , Binds(..)
   , Bind(..)
   , Alts
   , Alt(..)
   , Pat(..)
   , Literal(..)
   , Con(..)
   , Arity
   , idFromString
   , private
   , public 
   , dummyId
   , newNameSupply
   , stringFromId
   )
import CorePretty (corePretty) 
import CoreToAsm  (coreToAsm)
import PPrint (Doc) 
import Byte (bytesFromString)
import CoreParse (Kind (..), ppKind, Type (..), ppType) -- XXX weird place to get this from
import Standard   ( getLvmPath, searchPath, searchPathMaybe )
import CoreRemoveDead( coreRemoveDead ) -- remove dead declarations
import CoreToAsm  ( coreToAsm )         -- enriched lambda expressions (Core) to Asm

import AsmPretty  ( asmPretty )         -- pretty print low-level core (Asm)
import AsmOptimize( asmOptimize )       -- optimize Asm (ie. local inlining)
import AsmToLvm   ( asmToLvm )          -- translate Asm to Lvm instructions

import LvmPretty  ( lvmPretty )         -- pretty print instructions (Lvm)
import LvmWrite   ( lvmWriteFile )      -- write a binary Lvm file
import LvmImport  ( lvmImport )         -- resolve import declarations
import LvmRead    ( lvmReadFile )
import Data.Char  ( isUpper, isLower )

--------------------------------------------------------------------------------

-- XXX export and import decls need handling

-- Translates a program in the internal syntax into a String representing a
-- Scheme source file.
toLvmCore :: String -> AI.Prog -> IO () 
toLvmCore sourceName prog = do 
   putStrLnBanner ("src code") 
   print prog
   lvmPath       <- getLvmPath
   let path      = "." : lvmPath
   let biProg    = pProg prog
       mod       = toModule biProg
   putStrLnBanner ("basic transform")
   print $ corePretty mod 
   nameSupply <- newNameSupply
   putStrLnBanner ("gen asm")
   let asmmod    = coreToAsm nameSupply mod 
   print $ asmPretty asmmod
   putStrLnBanner ("asm opt")
   let    asmopt    = asmOptimize asmmod
   print $ asmPretty asmopt 
   putStrLnBanner ("lvm gen")
   let    lvmmod    = asmToLvm  asmopt
   print $ lvmPretty lvmmod
   let target    = reverse (dropWhile (/='.') (reverse sourceName)) ++ "lvm"
   lvmWriteFile target lvmmod

putStrLnBanner str = do
   putStrLn "##################################################################"
   putStrLn str


findModule paths id
  = searchPath paths ".lvm" (stringFromId id)

 
toModule :: BI.Prog -> CoreModule 
toModule (Prog (mod:_))  -- XXX assume only one module
   = Core.Module 
     { moduleName     = toCoreId $ moduleId mod
     , moduleMajorVer = 0 -- XXX what to do about these numbers?
     , moduleMinorVer = 0
     -- , moduleDecls    = primImport : primAbs : (concatMap toCoreDecls $ moduleDecs mod)
     , moduleDecls    = prims ++ (concatMap toCoreDecls $ moduleDecs mod)
     -- , moduleDecls    = importDecls ++ valDecls  
     }
   where
   valDecls    = concatMap toCoreDecls $ moduleDecs mod
   importDecls = concatMap toImportDecl $ moduleImports mod

-- data Import = Import Id Qual Imports
toImportDecl :: AI.Import -> [CoreDecl]
toImportDecl (Import modName qual imports)
   = importsToImportDecl imports
   where
   importsToImportDecl :: AI.Imports -> [CoreDecl]
   importsToImportDecl ImAll = [] -- error $ "toImportDecl: found ImAll"
   importsToImportDecl (ImSome specs)   = concatMap specToImportDecl specs
   importsToImportDecl (ImHiding specs) = [] -- error $ "toImportDecl: found ImHiding"
   specToImportDecl :: ImSpec -> [CoreDecl]
   specToImportDecl (ImVar id) 
      = [idToImportDecl id]
   specToImportDecl (ImCon id conSpec)
      = conSpecToDecl conSpec
   conSpecToDecl :: ConSpec -> [CoreDecl]
   conSpecToDecl AllCon = error $ "conSpecToDecl: AllCon"
   conSpecToDecl (SomeCon ids) = map idToImportDecl ids
   idToImportDecl :: AI.Id -> CoreDecl
   idToImportDecl id
      = DeclImport
          { declName    = toCoreId id
          , declAccess  = idAccess id
          , declCustoms = []
          }
   idAccess :: AI.Id -> Core.Access
   idAccess id
      = Imported
        { accessPublic   = True
        , importModule   = toCoreId modName
        , importName     = toCoreId id
        , importKind     = idKind id 
        , importMajorVer = 0  -- XXX what to do with these numbers?
        , importMinorVer = 0
        }

{-
data Id = Id { idSrcInfo :: SrcInfo, -- ^ source location info. 
               idStr     :: IdStr,   -- ^ the string name (eventually qualified)
               idOrigStr :: IdStr    -- ^ the original name 
          }
    deriving (Eq, Ord, Show, Read) -
-}
  
-- use the original name to find out if something is a con
-- or a value, rather than the qual name
-- Assumption: Haskell rules about names of variables and names of constructors
idKind :: AI.Id -> Core.DeclKind
idKind id
   | isConName $ idOrigStr id = DeclKindCon
   | isValName $ idOrigStr id = DeclKindValue 
   | otherwise = error $ "idKind: unknown kind of name: " ++ show id
   where
   -- XXX assume they might have module qualifiers
   isConName, isValName :: String -> Bool
   isConName str = isConStart $ firstCharOfName str
   isValName str = isValStart $ firstCharOfName str
   firstCharOfName :: String -> Char
   firstCharOfName str = head $ reverse $ takeWhile (/= '.') $ reverse str 
   isConStart :: Char -> Bool
   isConStart c = isUpper c || c == ':' 
   isValStart c = isLower c
  

-- Imported { accessPublic :: !Bool, importModule :: Id, importName :: Id, importKind :: !DeclKind             , importMajorVer :: !Int, importMinorVer :: !Int }




toCoreId id = idFromString $ idStr id 

toCoreDecls :: BI.Dec -> [CoreDecl]
toCoreDecls (ValDec { decLetBnd = letBnd })
   = [letBndToCoreDecl letBnd]
   where
   letBndToCoreDecl :: LetBnd -> CoreDecl
   letBndToCoreDecl (LetBnd _info id exp)
      = DeclValue
        { declName    = toCoreId id 
        , declAccess  = public 
        , valueEnc    = Nothing -- XXX what is this field for?
        , valueValue  = toCoreExpr exp 
        , declCustoms = []
        } 

toCoreDecls decl@(DataDec { decDataType = dataType, decConss = conss })
   = datadecl:conDecls
   where
   id   = idFromDataType dataType 
   args = dataTypeArgs dataType
   kind       = foldr KFun KStar (map (const KStar) args)
   tp         = foldl TAp (TCon id) (map (TVar . typeVarToId) args)
   datadecl   = DeclCustom id public customData [customKind kind]
   link       = CustomLink id customData
   conDecls   = zipWith (toConDecl tp link) [0..] conss
   customData = DeclKindCustom (idFromString "data") 
   customKind k 
      = CustomDecl (DeclKindCustom (idFromString "kind")) 
                   [CustomBytes (bytesFromString (show (ppKind k)))]

toCoreDecls decl@(PrimDec { decPrimVal = primVal })
--    = error $ show decl
   = [ abstractPrimDecl primVal ]
   where
   abstractPrimDecl :: BI.PrimVal -> CoreDecl
   -- XXX what is the external name for? 
   abstractPrimDecl (Prim id externName typeScheme) 
      = DeclAbstract 
        { declName    = coreId 
        , declAccess  = primitiveAccess coreId
        , declArity   = arityFromTypeScheme typeScheme
        , declCustoms = []
        } 
      where
      coreId = toCoreId id

primitiveAccess :: Core.Id -> Access 
primitiveAccess id 
   = Imported 
        { accessPublic   = True
        , importModule   = idFromString "Prim"  -- XXX Magic name for the prims module
        , importName     = id
        , importKind     = DeclKindValue
        , importMajorVer = 0
        , importMinorVer = 0
        }


arityFromTypeScheme :: TSchm -> Arity
arityFromTypeScheme (TSchm ctxt t)
   = arityFromType t
arityFromType :: BI.Type -> Arity
arityFromType (VarType _id) = 0
arityFromType (ConType _id) = 0
arityFromType (AppType _info1 (AppType _info2 tyCon _arg1) arg2)
   | isFunTyCon tyCon = 1 + arityFromType arg2 
   | otherwise = 0
   where
   isFunTyCon :: BI.Type -> Bool
   isFunTyCon (ConType id) = idOrigStr id == "->"
   isFunTyCon otherType = False
arityFromType otherType = 0


toConDecl :: CoreParse.Type -> Custom -> Int -> Cons -> CoreDecl
toConDecl tp link tag con 
   = dataTypeToCoreDecl $ consDataType con 
   where
   dataTypeToCoreDecl :: AI.DataType -> CoreDecl
   dataTypeToCoreDecl (AI.DataType id typeArgs) 
      = DeclCon coreId public (length typeArgs) tag [ctype, link]
      where
      coreId = toCoreId id
      ctype = customType $ foldr TFun tp $ map toCoreType typeArgs
      customType tp   
         = CustomDecl (DeclKindCustom (idFromString "type")) 
              [CustomBytes (bytesFromString (show (ppType tp)))]

{-
data Type  = VarType Id 
           | ConType Id
           | AppType SrcInfo Type Type

data Type       = TFun    {tp1::Type, tp2::Type}
                | TAp     {tp1::Type, tp2::Type}
                | TForall {tpId::Id, tp::Type}
                | TExist  {tpId::Id, tp::Type}
                | TStrict {tp::Type}
                | TVar    {tpId::Id}
                | TCon    {tpId::Id}
                | TAny
                | TString {tpString::String} 
                deriving (Show)
-}

toCoreType :: AI.Type -> CoreParse.Type
toCoreType (AI.VarType id) = TVar { tpId = toCoreId id }
toCoreType (AI.ConType id) = TCon { tpId = toCoreId id }
toCoreType (AI.AppType _info t1 t2)
   = TAp { tp1 = toCoreType t1, tp2 = toCoreType t2 }

typeVarToId :: AI.Type -> Core.Id
typeVarToId (AI.VarType id) = toCoreId id


dataTypeArgs :: AI.DataType -> [AI.Type]
dataTypeArgs (AI.DataType id typeArgs) = typeArgs

idFromDataType :: AI.DataType -> Core.Id
idFromDataType (AI.DataType id _args) = toCoreId id 

toCoreExpr :: Exp -> Core.Expr
toCoreExpr (VarExp id) 
   = Var $ toCoreId id
toCoreExpr (ConExp id) 
   = Con $ ConId $ toCoreId id
toCoreExpr (LitExp lit) 
   = Lit $ toCoreLiteral lit
toCoreExpr (AppExp _info e1 e2) 
   = Ap (toCoreExpr e1) (toCoreExpr e2)
toCoreExpr (AbsExp _info id e) 
   = Lam (toCoreId id) (toCoreExpr e) 
toCoreExpr (LetExp _info binds e)
   = Let (toCoreBinds binds) (toCoreExpr e) 
toCoreExpr (CaseExp _info (e:_) matches@(m:ms))      -- XXX assume one scrutinee
   | isVarPat firstMatchPat = Let firstMatchBind (toCoreExpr firstMatchBody)
   | isVarExp e = Core.Match (expVarId e) $ toCoreAlts matches
   | otherwise
        = Let scrutineeBind (Core.Match dummyId $ toCoreAlts matches)
   where
   scrutineeBind = NonRec (Bind dummyId (toCoreExpr e))   
   firstMatchBind = NonRec (Bind (patVarId firstMatchPat) (toCoreExpr e))   
   BI.Match (firstMatchPat:_) firstMatchBody = m 
toCoreExpr other = error $ show other

isVarExp :: BI.Exp -> Bool
isVarExp (VarExp _id) = True
isVarExp other      = False

expVarId :: BI.Exp -> Core.Id
expVarId (VarExp id) = toCoreId id

patVarId :: AI.Pat -> Core.Id
patVarId (AI.VarPat id) = toCoreId id

isVarPat :: AI.Pat -> Bool
isVarPat (AI.VarPat _id) = True
isVarPat other      = False

toCoreBinds :: [LetBnd] -> Core.Binds
toCoreBinds binds
   = Rec $ map letToCoreBind binds
   where
   letToCoreBind :: LetBnd -> Core.Bind
   letToCoreBind (LetBnd _into id e) 
      = Bind (toCoreId id) (toCoreExpr e) 

toCoreAlts :: [BI.Match] -> Core.Alts
toCoreAlts 
   = map matchToAlt 
   where
   matchToAlt :: BI.Match -> Core.Alt
   matchToAlt (BI.Match (pat:_) e) -- XXX assume one pat
      = Alt (toCorePat pat) (toCoreExpr e) 

{-
data Lit = IntegerLit SrcInfo Integer String
         | IntLit SrcInfo Int
         | FloatLit SrcInfo Double (Integer, Integer) String
         | StrLit SrcInfo String
         | CharLit  SrcInfo Char

data Literal    = LitInt    !Int
                | LitDouble !Double
                | LitBytes  !Bytes
-}

toCoreLiteral :: Lit -> Core.Literal
toCoreLiteral (AI.IntegerLit _info i _str)
   = LitInt $ fromIntegral i
toCoreLiteral (AI.IntLit _info i) = LitInt i
toCoreLiteral (AI.FloatLit _info d _rat _str) = LitDouble d
toCoreLiteral (AI.StrLit _info str)
   = LitBytes $ bytesFromString str 
toCoreLiteral (AI.CharLit _info c)
   = LitInt $ fromEnum c

{-
data Pat = VarPat Id
         | LitPat Lit
         | ConPat SrcInfo Id [Pat]

data Pat        = PatCon    !(Con Tag) ![Id]
                | PatLit    !Literal
                | PatDefault
-}

toCorePat :: AI.Pat -> Core.Pat
toCorePat (AI.VarPat id) 
   = PatDefault
toCorePat (AI.LitPat lit) 
   = PatLit $ toCoreLiteral lit
toCorePat (AI.ConPat _into conId varPats)
   = PatCon (ConId $ toCoreId conId) $ map varPatToCoreId varPats
   where
   varPatToCoreId :: AI.Pat -> Core.Id
   varPatToCoreId (AI.VarPat id) = toCoreId id
   varPatToCoreId other = dummyId 


{-
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
-}

-- prims

prims = [prim1Abs, prim2Abs, prim1Import, prim2Import]


prim1Abs
   = DeclAbstract 
     { declName = idFromString "primError"
     , declAccess = access1
     , declArity = 1
     , declCustoms = [] 
     }

access1 = Imported { accessPublic = True
                  , importModule = idFromString "Prims"
                  , importName = idFromString "primError"
                  , importKind = DeclKindValue
                  , importMajorVer = 0
                  , importMinorVer = 0
                  }
prim1Import 
   = DeclImport 
     { declName = idFromString "primError"
     , declAccess = access1 
     , declCustoms = [] 
     }

prim2Abs
   = DeclAbstract 
     { declName = idFromString "Chameleon.Primitive.patternMatchFailed"
     , declAccess = access2
     , declArity = 0
     , declCustoms = [] 
     }

access2 = Imported { accessPublic = True
                  , importModule = idFromString "Prims"
                  , importName = idFromString "patternMatchFailed"
                  , importKind = DeclKindValue
                  , importMajorVer = 0
                  , importMinorVer = 0
                  }
prim2Import 
   = DeclImport 
     { declName = idFromString "Chameleon.Primitive.patternMatchFailed"
     , declAccess = access2
     , declCustoms = [] 
     }
