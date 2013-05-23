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


--------------------------------------------------------------------------------
----
-- Parser for Chameleon
-- (now returns annotated AST... as per Ann_InputAST)
--
----
-- Notes:
--  - infix function identifiers cannot contain '(', ')', '[', or ']'
--  
----
-------------------------------------------------------------------
{

module AST.ChParser.Parser (
    parseProg, parseImportsOnly, parsePat 
)
where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import AST.ChParser.Lexer
import AST.ChParser.Tokens
import AST.ChParser.ParserMisc
import AST.External
import AST.SrcInfo
import AST.SrcCommand
import qualified AST.Token as AST

import Misc
import Misc.Result
import Misc.ErrorMsg
import Misc.Defaults

-- import IOExts

}

--------------------------------------------------------------------------------
-- Happy parser dec's.
-------------------------------------------------------------------
-- %name parserTyp Typ
-- %name parserExp Exp
-- %name parserSigTyp SigTyp
-- %name parserNestedRef NRef


%name parser Prog
%name parserModuleImports ModuleImports

%name parserPat Pat

%monad {P}
%lexer {lexer} {Teof}
%tokentype { Token }
%token
    id          { TId $$ }
    conid	{ TConId $$ }
    iid		{ TIId $$ }
    rule        { TRule $$ }
    overload    { TOverload $$ }
    class	{ TClass $$ }
    instance	{ TInstance $$ }
    data	{ TData $$ }
    type	{ TType $$ }
    hiding	{ THiding $$ }
    hconstraint	{ THConstraint $$ }
    constraint  { TConstraint $$ }
    deriving	{ TDeriving $$ }
    primitive	{ TPrimitive $$ }
    infix	{ TInfix $$ }
    infixl	{ TInfixl $$ }
    infixr	{ TInfixr $$ }
    ';'         { TSemicolon }
    '{'		{ TLBrace }
    '}'		{ TRBrace }
    '='         { TEquals $$ }
    '\\'        { TBackslash $$ }
    "->"        { TArrow $$ }
    if          { TIf $$ }
    then        { TThen $$ }
    else        { TElse $$ }
    let		{ TLet $$ }
    in		{ TIn $$ }
    case	{ TCase $$ }
    do		{ TDo $$ }
    of		{ TOf $$ }
    where	{ TWhere $$ }
    extern	{ TExtern $$ }
    module	{ TModule $$ }
    xmodule	{ TXModule $$ }
    import	{ TImport $$ }
    as		{ TAs $$ }
    qualified	{ TQualified $$ }
    forall	{ TForall $$ }
    '('         { TLParen $$ }
    ')'         { TRParen $$ }
    '['		{ TLBracket $$ }
    ']'		{ TRBracket $$ }
    ".."	{ TCont $$ }
    '_'         { TUnderscore $$ }
    '-'		{ TMinus $$ }
    "=>"	{ TImpl $$ }
    "==>"       { TPropArrow $$ }
    "<==>"	{ TSimpArrow $$ }
    ','         { TComma }
    '.'		{ TDot }
    '@'		{ TAt $$ }
    '|'		{ TBar $$ }
    '*' 	{ TAsterisk $$ }
    '?'		{ TQuestion $$ }
    "<-"	{ TLArrow $$ }
    "::"        { TAnn $$ }
    ":::"	{ TEAnn $$ }
    ":*:"	{ TRAnn $$ }
    "True"	{ TTrue $$ }
    "False"	{ TFalse $$ }
    "::?"	{ TQuery $$ }
    int		{ TInt $$ }
    float	{ TFloat $$ }
    char	{ TChar $$ }
    str		{ TStr $$ }
    "@_"        { TFunc $$ }
%% 

--------------------------------------------------------------------------------
-- Productions.
-------------------------------------------------------------------

-- Opens a layout block.
Open	:: { () }
	: '{'			    {()}

-- Closes a layout block. Note that a parse error at this point is equivalent
-- to a closing brace; we puch the previous token (which caused the error) back
-- onto the front of the token stream.
Close	:: { () }
	: '}'			    { () }
	| error			    {% dropContextEnd }


Ids	:: { [Id] }
	:			    { [] }
	| Ids id		    {% do { id <- mkNode mkId $2 (srcVal $2);
				            return (id : $1) } }

--------------------------------------------------------------------------------

-- NOTE: if there's no module header, we assume the default module name, and 
--       everything is exported 
Prog    :: { Prog }
	: AllDecs		    { let {(is,ds) = $1}
				      in  Prog [Module(anonId defaultModuleName)
						   ExAll is (reverse ds) Cmod ]}
	| Module		    { Prog [$1] }

Module  :: { Module }
	: xmodule Conid Exports where AllDecs
                                    { let {(is,ds) = $5}
                                      in  Module $2 $3 is (reverse ds) Xmod }
	| module Conid Exports where AllDecs 
				    { let {(is,ds) = $5}
				      in  Module $2 $3 is (reverse ds) Cmod }


AllDecs :: { ([Import], [Dec]) }
	: Open ImpDecs Close	    { $2 }

ImpDecs :: { ([Import], [Dec]) }
	: {- empty -}		    { ([], []) }
	| Import ';' ImpDecs	    { let {(is,ds) = $3}
				      in  ($1:is,ds) }
	| CmdDecs		    { ([], $1) }

----------------------------------------

Exports	:: { Exports }
	: {- empty -}		    { ExAll }
	| '(' ')'		    { ExSome [] }
	| '(' ExSpecs ')'	    { ExSome (reverse $2) }

ExSpecs	:: { [ExSpec] }
	: ExSpec		    { [$1] }
	| ExSpecs ',' ExSpec	    { $3 : $1 }

ExSpec  :: { ExSpec }
	: module Conid		    { ExModule $2 }
	| Var			    { ExVar $1 }
	| Conid ConSpec		    { ExCon $1 $2 }

----------------------------------------

Import  :: { Import }
	: ImMod Imports		    { $1 $2 }

ImMod	:: { Imports -> Import }
	: import Conid		    { Import $2 Unqual }
	| import qualified Conid    { Import $3 (Qual $3) }
	| import qualified Conid as Conid
				    { Import $3 (Qual $5) }

Imports	:: { Imports }
	: {- empty -}		    { ImAll }
	| hiding '(' ')'	    { ImAll }
	| hiding '(' ImSpecs ')'    { ImHiding (reverse $3) }
	| '(' ')'		    { ImSome [] }
	| '(' ImSpecs ')'	    { ImSome (reverse $2) }

ImSpecs	:: { [ImSpec] }
	: ImSpec		    { [] }
	| ImSpecs ',' ImSpec	    { $3 : $1 }

ImSpec  :: { ImSpec }
	: Var			    { ImVar $1 }
	| Conid ConSpec		    { ImCon $1 $2 }
	

ConSpec :: { ConSpec }
	: {- empty -}		    { SomeCon [] }
	| '(' ".." ')'		    { AllCon }
	| '(' CommaIds ')'	    { SomeCon (reverse $2) }

CommaIds:: { [Id] }
	: Id			    { [$1] }
	| CommaIds ',' Id	    { $3 : $1 }

----------------------------------------

-- Only use this from the top-level with an explicit open and close
TopDecs :: { [Dec] }
	: {- empty -}		    { [] }
	| CmdDecs		    { reverse $1 }

Decs	:: { [Dec] }
	: {- empty -}		    { [] }
	| Open CmdDecs Close	    { reverse $2 }


CmdDecs:: { [Dec] }
       : CmdDec			    { $1 }
       | CmdDecs ';' CmdDec	    { $3 ++ $1 }


CmdDec  :: { [Dec] }
	: Dec			    { $1 }


Dec     :: { [Dec] }
	: rule Rule		    {% mkNodes RuleDec $1 $2 }
	| data Data		    {% mkNodes DataDec $1 $2 }
	| type TypeSyn		    {% mkNodes TypeDec $1 $2 }
--	| overload Over		    {% mkNodes OverDec $1 $2 }
--	| extern Extern		    {% mkNodes ExtDec  $1 $2 }
	| class Class		    {% mkNodes ClassDec $1 $2 }
	| instance Inst		    {% mkNodes InstDec  $1 $2 }
	| primitive PrimVal	    {% mkNodes PrimDec $1 $2 }
        | constraint Pred           {% mkNodes ExtConsDec $1 $2 }
	| AnnDec		    { $1 }
	| Def			    {% mkNodes ValDec (extractSrc $1) [$1] }
	| PatBnd		    {% mkNodes PatDec (extractSrc $1) $1 }
	| FixDec		    {% mkNodes FixDec (fst $1) (snd $1) }

--------------------------------------------------------------------------------

PrimVal	:: { PrimVal }
	: Var "::" TSchm	    { Prim $1 (idStr $1) $3 }
	| Var str "::" TSchm	    { Prim $1 (srcVal $2) $4 }

--------------------------------------------------------------------------------

FixDec	:: { (Src String, Fixity) }
	: infix	 OptPrec CommaOps   { ($1, Fix NonAssoc $2 $3) }
	| infixl OptPrec CommaOps   { ($1, Fix LeftAssoc $2 $3) }
	| infixr OptPrec CommaOps   { ($1, Fix RightAssoc $2 $3) }

OptPrec :: { Int }
        :			    { 9 }	    -- default precedence
	| int			    { fromIntegral (fst (srcVal $1)) }

--------------------------------------------------------------------------------

Class	:: { Class }
--	: Pred ClassDecs	    { Class emptyCtxt $1 [] $2 }
--	| Pred FunDep ClassDecs     { Class emptyCtxt $1 $2 $3 }
--	| Type "=>" Pred ClassDecs  {% do{ctxt <- tupToCtxt $1;
--	                                  return (Class ctxt $3 [] $4)} }
--	| Type "=>" Pred FunDep ClassDecs  
--	                            {% do{ctxt <- tupToCtxt $1;
--	                                  return (Class ctxt $3 $4 $5)}	}
        : Pred WhereClassDecs		{% do{let {(a,b) = $2};
                                              case a of {
                                                [] -> return (Class emptyCtxt $1 [] b);
                                                _  -> return (AFDClass emptyCtxt $1 [] a b)} } }
        | Pred FunDep WhereClassDecs    {% do{let {(a,b) = $3};
                                              case a of {
                                                [] -> return (Class emptyCtxt $1 $2 b);
                                                _  -> return (AFDClass emptyCtxt $1 $2 a b)} } }
        | Type "=>" Pred WhereClassDecs {% do{ctxt <- tupToCtxt $1;
                                              let {(a,b) = $4};
                                              case a of {
                                                [] -> return (Class ctxt $3 [] b);
                                                _  -> return (AFDClass ctxt $3 [] a b)} } }
        | Type "=>" Pred FunDep WhereClassDecs {% do{ctxt <- tupToCtxt $1;
                                                     let {(a,b) = $5};
                                                     case a of {
                                                       [] -> return (Class ctxt $3 $4 b);
                                                       _  -> return (AFDClass ctxt $3 $4 a b)} } }


-- NOTE: maybe this should already be restricted to just parsing signatures
--	 (and default value declarations) 
ClassDecs :: { [Dec] }
	  : {- empty -}		    { [] }
	  | where Decs		    { $2 }

FunDep	:: { [FunDep] }
	: '|' FDs		    { reverse $2 }
	
FDs	:: { [FunDep] }
	: FD			    { [$1] }
	| FDs ',' FD		    { $3 : $1 }

FD	:: { FunDep }
	: Ids "->" Ids		    {% mkNode2 FunDep $2 (reverse $1) 
							 (reverse $3) }

WhereClassDecs :: { ([AFDDec],[Dec]) }
               : {- empty -}		       { ([],[]) }
               | where Open ClassCmdDecs Close {% do{let {(a,b) = $3};
                                                     return (reverse a,reverse b)} }

ClassCmdDecs :: { ([AFDDec],[Dec]) }
--             : CmdDecs              { ([],$1) }
-- being restrictive to only allow certain declarations
             : CCmdDecs             { ([],$1) }  
             | AFDDecs              { ($1,[]) }
--           | AFDDecs ';' CmdDecs  { ($1,$3) }
-- being restrictive to only allow certain declarations
             | AFDDecs ';' CCmdDecs  { ($1,$3) }

CCmdDecs :: { [Dec] }
	 : CCmdDec		    { $1 }
	 | CCmdDecs ';' CCmdDec	    { $3 ++ $1 }

CCmdDec :: { [Dec] }
	: AnnDec		    { $1 }
	| Def			    {% mkNodes ValDec (extractSrc $1) [$1] }
	| FixDec		    {% mkNodes FixDec (fst $1) (snd $1) }
-- adding more Decs here could lead to more conflicts

AFDDecs  :: { [AFDDec] }
         : AFDDec                   { [$1] }
         | AFDDecs ';' AFDDec       { $3 : $1 }

AFDDec   :: { AFDDec }
         : type Conid Ids             {% mkNode3 AFDDec $1 $2 (reverse $3) $2 }


--------------------------------------------------------------------------------

Inst	:: { Inst }
--	: Type "=>" Pred InstDecs   {% do{ctxt <- tupToCtxt $1;
--	                                  return (Inst ctxt $3 $4)} }
--	| Pred InstDecs		    { Inst emptyCtxt $1 $2 }
        : Type "=>" Pred WhereInstDecs    {% do{ctxt <- tupToCtxt $1;
                                                let {(a,b) = $4};
                                                case a of {
                                                  [] -> return (Inst ctxt $3 b);
                                                  _  -> return (AFDInst ctxt $3 a b)} } }
        | Pred WhereInstDecs              {% do{let {(a,b) = $2};
                                                case a of {
                                                  [] -> return (Inst emptyCtxt $1 b);
                                                  _  -> return (AFDInst emptyCtxt $1 a b)} } }

-- NOTE: maybe this should already be restricted to just parsing 
--	 value declarations
{- unused production
InstDecs :: { [Dec] }
	: {- empty -}		    { [] }
	| where Decs		    { $2 }
  -}
WhereInstDecs :: { ([AFDDef],[Dec]) }
              : {- empty -}	   	     { ([],[]) }
              | where Open InstCmdDecs Close {% do {let {(a,b) = $3};
                                                    return (reverse a,reverse b)} }

InstCmdDecs :: { ([AFDDef],[Dec]) }
--            : CmdDecs	   	  { ([],$1) }
-- being restrictive to only allow certain declarations
	    : ICmdDecs		  { ([],$1) }
            | AFDDefs             { ($1,[]) }
--            | AFDDefs ';' CmdDecs { ($1,$3) }
-- being restrictive to only allow certain declarations
            | AFDDefs ';' ICmdDecs { ($1,$3) }


ICmdDecs :: { [Dec] }
	 : ICmdDec		    { $1 }
	 | ICmdDecs ';' ICmdDec	    { $3 ++ $1 }

ICmdDec :: { [Dec] }
	: Def			    {% mkNodes ValDec (extractSrc $1) [$1] }
-- adding more Decs here could lead to more conflicts



AFDDefs :: { [AFDDef] }
        : AFDDef		{ [$1] }
        | AFDDefs ';' AFDDef	{ $3 : $1 }

AFDDef :: { AFDDef }
       : Conid TypeArgs '=' Type          {% mkNode3 AFDDef $3 $1 $2 $4 }

--------------------------------------------------------------------------------

IFace	:: { IFace }
	: Id			    { $1 }

--------------------------------------------------------------------------------

Over	:: { Over }
	: Var			    { Over0 $1 } 
	| Sig where Defs	    { OverDef $1 $3 }

--------------------------------------------------------------------------------

{-
Extern	:: { Extern }
	: ExternSig		    { VarExt  $1 }
	| Conid			    { TConExt $1 }

ExternSig :: { Sig }
	: Sig			    { $1 }
	| ConSig		    { $1 }

ConSig	:: { Sig }
	: Conid "::" TSchm	    { Sig [$1] Univ $3 }
-}

--------------------------------------------------------------------------------

-- NOTE: this is the source of a number of shift/reduce conflicts
Def     :: { Def }
	: Var Pats RHS Where	    { Def $1 $2 $3 $4 }
	| Pat Iid Pat RHS Where	    { Def $2 [$1,$3] $4 $5 }

RHS	:: { RHS }
	: '=' Exp		    { RHS1 $2 }
	| GdOpts		    { RHSG $1 }

GdOpts  :: { [GdExp] }
	: GdOpt			    { [$1] }
	| GdOpts GdOpt		    { $2 : $1 }

GdOpt	:: { GdExp }
	: '|' Exp '=' Exp	    {% mkNode2 GdExp $1 $2 $4 }
	
Where	:: { [Dec] }
	: {- empty -}		    {[]}
	| where Decs		    {reverse $2}
	
----------------------------------------

Defs	:: { [Def] }
	: Open DefBlk Close	    { reverse $2 }

DefBlk	:: { [Def] }
	: Def			    { [$1] }
	| DefBlk ';' Def	    { $3 : $1 }

--------------------------------------------------------------------------------

PatBnd	:: { PatBnd }
	: BndPat RHS Where	    { PatBnd $1 $2 $3 }

--------------------------------------------------------------------------------

Pat	:: { Pat }
	: ConPat		    { $1 }
	| AtomPat		    { $1 }
	| Id			    { VarPat $1 }
	| Id '@' Pat		    {% mkNode2 AsPat $2 $1 $3 }



-- NOTE: This includes all non-simple (single variable) patterns. These can
--	 appear on the LHS of a pattern binding.
BndPat	:: { Pat }
	: ConPat		    { $1 }
	| AtomPat		    { $1 }
	| Id '@' Pat		    {% mkNode2 AsPat $2 $1 $3 }

ConPat	:: { Pat }
	: '(' Conid Pats ')'	    {% mkNode2 ConPat (extractSrc $2) $2 $3 }
	| '(' IfxPat ')'	    { $2 }
	| Conid			    {% mkNode2 ConPat (extractSrc $1) $1 [] } 
	
IfxPat  :: { Pat }
	: Pat Iid Pat		    {% mkNode2 ConPat (extractSrc $2) 
						      $2 [$1, $3] }
	| Pat Iid IfxPat	    {% mkNode2 ConPat (extractSrc $2) 
						      $2 [$1, $3] }

AtomPat :: { Pat }
	: Lit			    { LitPat $1 }
	| Conid FieldPats	    { LabPat $1 $2 }
	| "True"		    {% do {true  <- mkNode mkId $1 "True";
					   {- trace ("true = " ++ show true) -} (mkNode2 ConPat $1 true [])} }
	| "False"		    {% do {false <- mkNode mkId $1 "False";
					   mkNode2 ConPat $1 false []} }
	| '[' ']'		    {% mkNode ListPat $1 [] }
	| '[' CommaPats ']'	    {% mkNode ListPat $1 $2 }
	| '(' CommaPats ')'	    {% mkNode TupPat $1  $2 }
	| '(' AtomPat ')'	    { $2 }
--      change for unit pattern
--	| '(' ')'		    {% mkNode TupPat $1 [] }
        | '(' ')'                   {% do {unit <- mkNode mkId $1 "()";
					 (mkNode2 ConPat $1 unit [])}}
	| '[' Pat ']'		    {% mkNode ListPat $1 [$2] }
--	| '(' Id as Type ')'	    {% mkNode2 AnnPat $3 $2 $4 } {- RegExp -}
	| '(' Id "::" Type ')'	    {% mkNode2 AnnPat $3 $2 $4 } {- This doesn't work -}


Pats	:: { [Pat] }
	: Pats_rev		    { reverse $1 }

Pats_rev:: { [Pat] }
	:			    { [] }
	| Pats_rev Pat		    { $2 : $1 }

CommaPats :: { [Pat] }
	: AppPat ',' AppPat	    { [$1,$3] }
	| AppPat ',' CommaPats	    { $1 : $3 }

AppPat	:: { Pat }
	: AppConPat		    { $1 }
	| AtomPat		    { $1 }
	| Id			    { VarPat $1 }

AppConPat :: { Pat }
	: '(' Conid Pats ')'        {% mkNode2 ConPat (extractSrc $2) $2 $3 }
	| '(' IfxPat ')'            { $2 }
	| Conid Pats		    {% mkNode2 ConPat (extractSrc $1) $1 $2 }
				    

--------------------------------------------------------------------------------


Exp	:: { Exp }
	: Exp1			    {$1}
	| Exp1 "::" TSchm	    {% mkNode3 AnnExp $2 $1 Univ $3 }
	| Exp1 ":::" TSchm	    {% mkNode3 AnnExp $2 $1 Exist $3 }
	| Exp1 ":*:" TSchm	    {% mkNode3 AnnExp $2 $1 Reg $3 }
{-	
	| Exp1 "::?"		    {% do {let {l  = ixLoc (ann $1)};
					   let {sc = SCTypeLoc l};
					   addCommand sc;
					   return $1} }
					   
	| Exp1 "::?" SigTyp	    {% do {let {l  = ixLoc (ann $1)};
					   let {(c,t) = $3};
					   let {ts = TSchm c t};
					   let {sc = SCExplainLoc l ts};
					   addCommand sc;
					   return $1} }
-}

Exp1	:: { Exp }
	: Exp0			    { $1 }
	| IfxExp		    { $1 }

IfxExp	:: { Exp }
	: Exp Iid Exp0		    {% mkNode3 IfxAppExp (extractSrc $2) 
							 $1 (VarExp $2) $3 }
	| '(' Exp Iid Exp0 ')'	    {% mkNode3 PIfxAppExp (extractSrc $3) 
							  $2 (VarExp $3) $4 }

Exp0	:: { Exp }
	: if Exp then Exp else Exp  {% do {f <- mkNode IfExp $1 $2;
					  mkNode2 f $3 $4 $6 } }

    	| '\\' Pats "->" Exp        {% mkNode2 AbsExp $1 $2 $4 }
	
	| App			    { $1 }

	| '-' App		    {% mkNode NegExp $1 $2 }

	| let Decs in Exp	    {% mkNode2 LetExp $1 $2 $4 }
	
	| case Exp of Open Alts Close 
				    {% mkNode2 CaseExp $1 $2 $5 }
						    
	| do Open SemiStmts Close   {% mkNode DoExp $1 $3 }
	

App	:: { Exp }
	: App AExp		    {% mkNode2 AppExp (extractSrc $1) $1 $2 }
	| AExp			    { $1 }
	

AExp	:: { Exp }
	: AExpXCon		    { $1 }
	| Conid                     { ConExp $1 }
	| Conid	FieldBinds	    { RecExp $1 $2 }
	| AExpXCon FieldBinds	    { UpdExp $1 $2 }
	
-- NOTE: We need to explicitly match the True and False tokens (they're
--	 distinct from Conids.)
AExpXCon:: { Exp }
	: Id                        { VarExp $1 }
	| "True"		    {% mkNestedNode ConExp mkId $1 "True" }
	| "False"		    {% mkNestedNode ConExp mkId $1 "False" }
	| '(' Iid ')'		    { VarExp $2 }
	| Lit			    { LitExp $1 }
	| '(' CommaExps ')'         {% case $2 of {
					[x] -> return (addInfixParens x);
					xs  -> mkNode TupExp $1 (reverse xs) } }
	| '(' Iid Exp ')'	    {% mkNode2 SecRightExp (extractSrc $2)
							   (VarExp $2) $3 }
	| '(' Exp Iid ')'	    {% mkNode2 SecLeftExp (extractSrc $3)
							   $2 (VarExp $3) }
--      change to unit constructor
--	| '(' ')'                   {% mkNode TupExp $1 [] }    
        | '(' ')'                   {% mkNestedNode ConExp mkId $1 "()" } 
	| '[' ListExp		    {% mkNode0 $2 $1 }
	| '[' ']'		    {% do {xs <- mkNode Many $1 [];
					   mkNode ListExp $1 xs} }

					   
-- NOTE: SrcInfo comes from the leading bracket, which is only available above
ListExp	:: { SrcInfo -> Exp }
	: Exp ']'		    {% do {xs<-mkNode Many (extractSrc $1) [$1];
					   return (\s -> ListExp s xs)} }
	| Exp ',' Exp ']'	    {% do {xs <- mkNode Many (extractSrc $1) 
							     [$1, $3];
					   return (\s -> ListExp s xs)} }
	| Exp ',' Exp ',' CommaExps ']'
				    {% do {xs <- mkNode Many (extractSrc $1) 
						    ([$1, $3] ++ reverse $5);
					   return (\s -> ListExp s xs)} }
	| Exp ".." ']'		    { \s -> EnumFromExp s $1 }
	| Exp ',' Exp ".." ']'	    { \s -> EnumFromThenExp s $1 $3 }
	| Exp ".." Exp ']'	    { \s -> EnumFromToExp s $1 $3 } 
	| Exp ',' Exp ".." Exp ']'  { \s -> EnumFromThenToExp s $1 $3 $5 } 
	| Exp '|' CommaStmts	    { \s -> ListCompExp s $1 $3 }
				       


CommaExps :: { [Exp] }
	: Exp			    { [$1] }
	| CommaExps ',' Exp	    { $3 : $1 }

----------------------------------------

CaseAlts:: { [CaseAlt] }
	: Alts			    { reverse $1 }

Alts	:: { [CaseAlt] }
	: Alt			    { $1 }
	| Alts ';' Alt		    { $3 ++ $1 }

Alt	:: { [CaseAlt] }
	: {- empty -}		    { [] }
	| Pat "->" Exp AltWhere	    {% do{n<-mkNode3 CaseAlt $2 $1 (RHS1 $3) $4;
					   return [n]} }
	| Pat GdPat AltWhere	    {% do {n<-mkNode3 CaseAlt 
						(extractSrc $2) $1 (RHSG $2) $3;
					   return [n]} }

GdPat	:: { [GdExp] } 
	: GdAlt "->" Exp GdPats	    {% do {n <- mkNode2 GdExp (extractSrc $1) 
							      $1 $3;
					   return (n:$4)} }
GdPats  :: { [GdExp] }
	: {- empty -}		    { [] }
	| GdPat			    { $1 }

GdAlt   :: { Exp }
        : '|' Exp		    { $2 }
	
AltWhere:: { Where }
	: {- empty -}		    { [] }
	| where Decs		    { $2 }


----------------------------------------

-- NOTE: the final statement must be an expression
SemiStmts :: { [Stmt] }
	: Exp			    {% do {n <- mkNode QualStmt 
						       (extractSrc $1) $1;
					   return [n]} }
	| ';' SemiStmts		    { $2 } -- empty statement
	| Stmt ';' SemiStmts	    { $1 : $3 }

CommaStmts :: { [Stmt] }
	: Stmt ']'		    { [$1] }
	| Stmt ',' CommaStmts	    { $1 : $3 }

Stmt	:: { Stmt }
	: let Decs 		    {% mkNode LetStmt $1 $2 }
	| Exp			    {% mkNode QualStmt (extractSrc $1) $1 }
	| Exp "<-" Exp		    {% mkNode2 GenStmt $2 (expToPat $1) $3 }
				  

--------------------------------------------------------------------------------

Lit	:: { Lit }
	: int			    {% let {(n,str) = srcVal $1}
				       in  mkNode2 IntegerLit $1 n str }
	| float			    {% let {(n,str,r) = srcVal $1}
				       in  mkNode3 FloatLit $1 n r str }
	| str			    {% mkNode StrLit $1 (srcVal $1) }
	| char			    {% mkNode CharLit $1 (srcVal $1) }
	
--------------------------------------------------------------------------------

AnnDec  :: { [Dec] }
	: Sigs				    {% mapM (\x -> mkNode AnnDec
						    (extractSrc x) x) $1}

CommaVars :: { [Id] }
	: Var				    { [$1] }
	| CommaVars ',' Var		    { $3 : $1 } 

Sigs	:: { [Sig] }
	: CommaVars "::"  TSchm		    { map (\x -> Sig x Univ $3) 
						  (reverse $1) }
	| CommaVars ":::" TSchm		    { map (\x -> Sig x Exist $3) 
						  (reverse $1) }
	| CommaVars ":*:" TSchm		    { map (\x -> Sig x Reg $3) 
						  (reverse $1) }
-- These three rules are reported as unused. We need to verify.
Sig	:: { Sig }
	: Var "::"  TSchm		    { Sig $1 Univ $3 }
	| Var ":::" TSchm		    { Sig $1 Exist $3 }
	| Var ":*:" TSchm		    { Sig $1 Reg $3 }

-- parse the context as a type
TSchm   :: { TSchm }
	: Type				    { TSchm emptyCtxt $1 }
	
	| Type "=>" Type		    {% do {ctxt <- tupToCtxt $1;
						   return (TSchm ctxt $3)} }
	
--------------------------------------------------------------------------------

TypeSyn :: { TSyn }
	: conid Ids '=' Type	{% do{id <- mkNode mkId $1 (srcVal $1);
					  return (TSyn id $2 $4)} }

--------------------------------------------------------------------------------

Data	:: { Data }
	: conid Ids ConDecs Deriv   {% mkNestedNode4 Data mkId $1 (srcVal $1) 
	                                             (reverse $2) $3 $4}
        | conid KAnns ConDecs Deriv {% mkNestedNode4 DataKindAnn mkId $1 (srcVal $1)
                                                     (reverse $2) $3 $4}
        -- added for unit type declaration
	| '(' ')' ConDecs Deriv {% mkNestedNode4 Data mkId $1 "()" [] $3 $4}

				    
KAnns   :: { [Type] }
        : KAnns KAnnAtom            { $2 : $1 }
        | KAnnAtom                  { $1 : [] }

KAnnAtom :: { Type }
         : '(' id ')'               {% mkNestedNode VarType mkId $2 (srcVal $2) }
         | '(' Id "::" Kind ')'     {% mkNode2 AnnType $3 $2 $4 }

Deriv   :: { Deriv }
        : {- empty -}               { Deriv [] }
        | deriving Derivs           { $2 }
        
Derivs  :: { Deriv }
        : Conid                     { Deriv [$1] }
        | '(' CommaConids ')'       { Deriv $2 }

CommaConids:: { [Id] }
        : CommaConids_rev           { reverse $1 }

CommaConids_rev :: { [Id] }
        : Conid                     { [$1] }
        | CommaConids_rev ',' Conid { $3 : $1 }


ConDecs	:: { [Con] }
	:			    { [] }
	| '=' Cons		    { reverse $2 }

Cons	:: { [Con] }
	: QntCon		    { [$1] }
	| Cons '|' QntCon	    { $3 : $1 }

QntCon:: { Con }
	: CtxtCon		    { $1 }
	
	-- FIXME: iid must be a dot! '.'
	| forall Ids iid CtxtCon    { addExistVarsCon $2 $4 }

	
CtxtCon :: { Con }
	: '(' Cnst ')' "=>" conid AtomTypes 
				    {% do { con <- mkNestedNode2 Con mkId $5 
						    (srcVal $5) (reverse $6);
					    return (addCnstCon $2 con)} }
	| '(' Cnst ')' "=>" conid '{' FieldDefs '}'
				    {% do {con <- mkNestedNode2 RecCon mkId $5 
						    (srcVal $5) $7;
					   return (addCnstCon $2 con)} }
				    
	| MaybeCon		    { $1 }

MaybeCon:: { Con }
	: conid FieldDefs	    {% mkNestedNode2 RecCon mkId $1
						    (srcVal $1) $2 }
	| conid AtomTypes ConBits   {% case $3 of {
					Nothing -> mkNestedNode2 Con mkId $1 
						    (srcVal $1) (reverse $2);
					Just con -> do {
					    -- let {t = combineTypes (reverse $2)};
					    p <- mkNode2 Pred $1 
						   (anonId (srcVal $1)) (reverse $2);
					    let {cnst = Cnst [PredPrim p]};
					    return (addCnstCon cnst con)}} }
        -- added for unit constructor
	| '(' ')'                   {% mkNestedNode2 Con mkId $1 "()" [] }
					    
ConBits	:: { Maybe Con }
	: {- empty -}		    { Nothing }
	| "=>" conid AtomTypes	    {% do {con <- mkNestedNode2 Con mkId $2 
						    (srcVal $2) (reverse $3);
					   return (Just con)} }
	| "=>" conid FieldDefs	    {% do {con <- mkNestedNode2 RecCon mkId $2
						    (srcVal $2) $3;
					   return (Just con)} }

FieldDefs :: { [FieldDef] }
	: '{' '}'		    { [] }
	| '{' CommaFieldDefs '}'    { concat (reverse $2) }

FieldDef:: { [FieldDef] }
	: CommaVars "::" Type	    { map (flip FieldDef $3) (reverse $1) }

CommaFieldDefs :: { [[FieldDef]] }
	: FieldDef		    { [$1] }
	| CommaFieldDefs ',' FieldDef
				    { $3 : $1 }

----------------------------------------

FieldBinds :: { [FieldBind] }
	: '{' '}'		    { [] }
	| '{' CommaFieldBinds '}'   { reverse $2 }

CommaFieldBinds :: { [FieldBind] }
	: FieldBind		    { [$1] }
	| CommaFieldBinds ',' FieldBind
				    { $3 : $1 }

FieldBind :: { FieldBind }
	: Var '=' Exp		    {% mkNode2 FieldBind $2 $1 $3 }

----------------------------------------

FieldPats :: { [FieldPat] }
	: '{' '}'		    { [] }
	| '{' CommaFieldPats '}'    { reverse $2 }

CommaFieldPats :: { [FieldPat] }
	: FieldPat		    { [$1] }
	| CommaFieldPats ',' FieldPat
				    { $3 : $1 }

-- NOTE: we allow punning
FieldPat :: { FieldPat }
	: Var '=' Pat		    {% mkNode2 FieldPat $2 $1 $3 }
	| Var			    {% mkNode2 FieldPat (extractSrc $1) 
							$1 (VarPat $1) }

--------------------------------------------------------------------------------

Rule	:: { Rule }
	: PropRule		    {$1}
	| SimpRule		    {$1}

PropRule :: { Rule }
	 : Ctxt "==>" Cnst	    { PropRule $1 $3 }
	 
SimpRule :: { Rule }
	 : Ctxt "<==>" Cnst	    { SimpRule $1 $3 }

Ctxt	:: { Ctxt }
	: Preds			    { Ctxt (reverse $1) }

Cnst	:: { Cnst }
	: Prims			    { let c = Cnst (reverse $1) in 
				      {-trace ("c: " ++ show c)-} c }

Preds   :: { [Pred] }
	: Pred			    { [$1] }
        | Preds ',' Pred	    { $3 : $1 }

Prims   :: { [Prim] }
	: Prim			    { [$1] }
        | Prims ',' Prim	    { $3 : $1 }


Pred    :: { Pred }
	: "True"		    {% mkNode2 Pred $1 (anonId "True") 
						       (error "Pred.TRUE!") }
	| "False"		    {% mkNode2 Pred $1 (anonId "False") 
						       (error "Pred.FALSE!") }
	
	| Type   		    {% typeToPred $1 }


-- We immediately desugar True and False predicates into equations.
-- NOTE: this should probably wait until the Desugar module
Prim	:: { Prim }
	: Pred			    { case (isTruePred $1, isFalsePred $1) of{
					(True,_) -> mkTrueEqPrim $1;
					(_,True) -> mkFalseEqPrim $1;
					_ -> PredPrim $1} }

        | Type '=' Type		    -- {% mkNode2 EqPrim (extractSrc $1) $1 $3 }
				    {% mkNode2 EqPrim $2 $1 $3 }


------------------------------------------------------------------------------

Type	:: { Type }
	: AppType		    { $1 }
	| IfxType		    { $1 }

IfxType	:: { Type }
	: AppType "->" Type	    {% mkNode2 ArrType $2 $1 $3 }

	| Type iid AppType	    {% do {t1 <- mkNestedNode ConType mkId $2 
							      (srcVal $2);
					   t2 <- mkNode2 AppType $2 t1 $1;
					   mkNode2 AppType $2 t2 $3} }
	
AppType	:: { Type }
	: AppType AtomType	    {% mkNode2 AppType (extractSrc $1) $1 $2 } 
	
	| AtomType		    { $1 }

AtomType:: { Type }
	: id			    {% mkNestedNode VarType mkId $1 (srcVal $1) }

	| '(' iid ')'		    {% mkNestedNode ConType mkId $2 (srcVal $2) }
	
	| '(' "->" ')'		    {% mkNestedNode ConType mkId $1 "->" }
--      change for unit type
--	| '(' ')'		    {% mkNode TupType $1 [] }

        | '(' ')'                   {% mkNestedNode ConType mkId $1 "()" }
	
        | conid			    {% mkNestedNode ConType mkId $1 (srcVal $1) }
	
	| '(' TupTypes ')'	    {% mkNode TupType $1 (reverse $2) }

	| '(' UnionTypes ')'	    {% mkNode UnionType $1 (reverse $2) } {- RegExp -}
	
	| '[' Type ']'		    {% mkNode ListType $1 $2 }
	
	| '[' ']'		    {% mkNestedNode ConType mkId $1 "[]" }
					  
	| '(' Type ')'		    { $2 }

--	|  Type '*'                 {% mkNode StarType $2 $1 }   {- RegExp -}

	| '(' Type '*' ')'          {% mkNode StarType $3 $2 }   {- removes r/r conflicts -}

--	|  Type '?'		    {% mkNode OptionType $2 $1 } {- RegExp -}

	| '(' Type '?' ')'	    {% mkNode OptionType $3 $2 } {- removes r/r conflicts -}

	| '(' Id "::" Kind ')'      {% mkNode2 AnnType $3 $2 $4 }


--        | '(' '@' id TypeArgs ')' {% do { myId <- mkNode mkId $3 ("@" ++ (srcVal $3));
--                                          mkNode2 FuncType $2 myId $4 } }

TypeArgs :: { [Type] }
         : Type ',' TypeArgs { $1 : $3 }
         | Type { [$1] }
         | {- empty -}   { [] }

TupTypes	:: { [Type] }
--	: Type			    { [$1] } 
	: Type ',' Type		    { $3 : [$1] }		{- remove s/r conflict -}
	| TupTypes ',' Type	    { $3 : $1 }

UnionTypes :: { [Type] }					 {- RegExp -}
	   : Type '|' Type          { $3 : [$1] }
	   | UnionTypes '|' Type    { $3 : $1 }

AtomTypes :: { [Type] }
	  :                         { [] }
          | AtomTypes AtomType      { $2 : $1 }

--------------------------------------------------------------------------------

Kind    :: { Type }
        : '*'                          {% mkNestedNode ConType mkId $1 (srcVal $1)}
        | Kind "->" Kind               {% mkNode2 ArrType $2 $1 $3 } 
        | '(' Kind ')'                 { $2 }

--------------------------------------------------------------------------------

Var	:: { Id }
	: Id				    { $1 }
	| '(' Iid ')'			    { $2 }

Conid	:: { Id }
	: conid				    {% mkNode mkId $1 (srcVal $1) }

Iid	:: { Id }
	: iid				    {% mkNode mkId $1 (srcVal $1) }
        | '*'                               {% mkNode mkId $1 (srcVal $1) }
--        | '-'                               {% mkNode mkId $1 (srcVal $1) }

Id	:: { Id }
	: id				    {% mkNode mkId $1 (srcVal $1) }
	
Op	:: { Id }
	: Iid				    { $1 }

CommaOps :: { [Id] }
	: CommaOps_rev			    { reverse $1 }

CommaOps_rev :: { [Id] }
	: Op				    { [$1] }
	| CommaOps_rev ',' Op		    { $3 : $1 }
	

--------------------------------------------------------------------------------
-- A parser for module imports. Returns just the import declarations in the
-- given module.

ModuleImports :: { [Import] } 
	: {- empty -}			    { [] }
	| MIImpDecs			    { $1 }

MIImpDecs :: { [Import] }
	: Import			    { [$1] }
	| Import ';' MIImpDecs		    { $1 : $3 }
{-
MIDecs  :: { () }
	: error				    { bug "module imports decs" }
	| '}'				    
-}

{-

AnnDec	:: { [Dec] }
	: Dec			    {% if null $1
					then return []
					else do { l <- newLabel;
						  return [Ann l (head $1)] } }
						  
				    
	| Var "::?" ';' Def	    {% do{l1 <- newLabel;
					  l2 <- newLabel;
					  let {sc = SCTypeVar (idStr $1)
						     (ixLoc l2);};
					  addCommand sc;
					  return [Ann l2 (ValDec [Ann l1 $4])]}}

	| Var "::?" SigTyp ';' Def  {% do{l1 <- newLabel;
					  l2 <- newLabel;
					  let {(c,t) = $3;
					       ts = TSchm c t;
					       sc = SCExplainVar (idStr $1)
						     (ixLoc l2) ts};
					  addCommand sc;
					  return [Ann l2 (ValDec [Ann l1 $5])]}}

-}

					  
  


{

--------------------------------------------------------------------------------

-- Takes the filename, a starting number (for node labeling), and the string
-- to parse, and returns the remaining unparsed string, a list of source
-- commands, the next node number and the External AST, and the token stream
-- (or failure.)
parseProg :: String -> UniqueNum -> String 
	  -> SimpleResult (String, [SrcCommand], UniqueNum, Prog, [AST.Token])
parseProg fn n str = runPConf fn n str parser

-- takes the same arguments as parseProg above
-- NOTE: obviously there're no src commands to return 
--	 (tokens are also unimportant in this case.)
parseImportsOnly :: String -> UniqueNum -> String
		 -> SimpleResult (String, UniqueNum, [Import])
parseImportsOnly fn n str = 
    case runPConf fn n str (useModImportMode >> parserModuleImports) of
	Failure e b -> Failure e b
	Success e (str, _scs, u, p, _tok) -> Success e (str, u, p)

----------------------------------------

parsePat s = runP s (interactiveParser >> parserPat)

interactiveParser = dontHandleLayout >> dontExitOnFail

{-
parseInit fn s n = runPNum fn s parser n


parseTyp s = runP s $ do interactiveParser
			 typ <- parserTyp
			 l   <- newLabel
			 return (Ann l typ)

parseExp n s = flip (runPNum_ s) n $ do interactiveParser
				        parserExp

parseTSchm n s = flip (runPNum_ s) n $ do interactiveParser
					  (c, t) <- parserSigTyp
					  l1 <- newLabel
					  return (Ann l1 (TSchm c t))

parseNestedRef n s = flip (runPNum_ s) n $ do interactiveParser
					      parserNestedRef

-}

-- called on an error (if the error token is unexpected)
happyError :: P a
happyError = do 
    l <- getLineNum
    c <- getColNum
    fn <- getFileName
    s <- getPrevInput
    (t,_,_) <- getPrevToken
    let msg = let s = SrcInfo { srcLoc = -1, -- filler "srcLoc", 
				srcFile = fn,
				srcRow = l, srcCol = c, srcOffset = -98 }
	      in  errorMsg s ["Parse error, unexpected token: `"++show t++"'"]
    setInput ""
    fail msg

}
