{
module IML.Parser.HappyParser where

import IML.Lexer (Token(..), lexer)
import IML.Parser.Shared
import IML.Grammar.Shared
import IML.Grammar.High
import IML.Grammar.Programs
import IML.Grammar.Specs
import IML.Trans.ProMan

import qualified Funcons.Operations as VOP

import Data.Text (pack, unpack)
import Data.String (fromString)

}

%name happy_parser
%tokentype { Token }
%error { (error . show) }


%token ID         { IDLit (Just $$) }
%token INT        { IntLit (Just $$) }
%token STRING     { StringLit (Just $$) }
%token CHAR       { CharLit (Just $$)}
%token ALT        { AltIDLit (Just $$) }
%token RELSYMB    { Token "REL-SYMB" (Just $$)}
%token BAR        { Token "BAR" (Just $$) }

%token '>' { Char '>' }
%token '<' { Char '<' }
%token '[' { Char '[' }
%token ']' { Char ']' }
%token ')' { Char ')' }
%token '(' { Char '(' }
%token '{' { Char '{' }
%token '}' { Char '}' }
%token ',' { Char ',' }
%token '-' { Char '-' }
%token '_' { Char '_' }
%token '*' { Char '*' }
%token '#' { Char '#' }
%token '=' { Char '=' }
%token '?' { Char '?' }

%token 'RESET-BINDINGS'   { Keyword "RESET-BINDINGS" }
%token 'with'             { Keyword "with" }
%token 'seq-variable'     { Keyword "seq-variable" }
%token 'is-terminal'      { Keyword "is-terminal" }
%token 'is-non-terminal'  { Keyword "is-non-terminal" }
%token 'repeatable'       { Keyword "repeatable" }
%token 'relation'         { Keyword "relation" }
%token 'entity'           { Keyword "entity" }
%token 'terminal'         { Keyword "terminal" } 
%token 'SHORTEST'         { Keyword "SHORTEST" }
%token 'LONGEST'          { Keyword "LONGEST" }
%token 'RANDOM'           { Keyword "RANDOM" }
%token 'BOOLEANS'         { Keyword "BOOLEANS" } 
%token 'ATOMS'            { Keyword "ATOMS" } 
%token 'VALUES'           { Keyword "VALUES" } 
%token 'MAPS'             { Keyword "MAPS" } 
%token 'STRINGS'          { Keyword "STRINGS" } 
%token 'INTEGERS'         { Keyword "INTEGERS" } 
%token 'CHARACTERS'       { Keyword "CHARACTERS" } 
%token 'LISTS'            { Keyword "LISTS" } 
%token 'SETS'             { Keyword "SETS" } 
%token 'TUPLES'           { Keyword "TUPLES" } 
%token 'TYPES'            { Keyword "TYPES" } 
%token 'ADTS'             { Keyword "ADTS" } 
%token '|-'               { Keyword "|-" }
%token '|>'               { Keyword "|>" }

%%

program : multiple(fragment)       { mkProgram $1 }

-- fragments
fragment : 'relation' parens(reldecl)       { FRelation $2 } 
         | 'entity' parens(entdecl)         { FEntity $2 }
         | 'terminal' parens(tconsdecl)     { FTermCons $2 }
         | inference                        { FRule $1 } 
         | query                            { FQuery $1 }
         | '>' 'RESET-BINDINGS'             { FResetEnv }

query : '>' premise vardecls       { Query $2 $3 }

reldecl : RELSYMB optional(reldeclAux)  { RelDecl $1 (maybe [] id $2) }
reldeclAux : ',' multipleSepBy1(prop,',') { $2 }
prop : 'repeatable' { Repeatable }

entdecl : ID ',' seq(expr) { EntDecl $1 $3 }

tconsdecl : RELSYMB ',' either(builtintype,ID) { PCTerm $1 $3 }
          | ID ',' either(builtintype,ID)      { EIDTerm $1 $3 }

builtintype : 'BOOLEANS' { Booleans } | 'ATOMS' { Atoms } | 'VALUES' { Values } |
              'MAPS' { Maps } | 'STRINGS' { Strings } | 'INTEGERS' { Integers } |
              'CHARACTERS' { Characters } | 'LISTS' { Lists } | 'SETS' { Sets } |
              'TUPLES' { Tuples } | 'TYPES' { Types } | 'ADTS' { ADTs }
 
-- configurations

-- variable declarations
vardecls :                           { [] }
         | 'with' multiple1(vardecl) { $2 }

vardecl : varConditions 'seq-variable' parens(vardeclAux) { $3 $1 }
vardeclAux : var ',' INT ',' maxbound optStrat   { VarDecl $1 $3 $5 $6 }
           | var ',' INT optStrat                { VarDecl $1 $3 Nothing $4 }
           | var optStrat                        { VarDecl $1 0 Nothing $2 }

varConditions : multiple1(condition) BAR   { $1 } 
              |                            { [] }

maxbound : INT { Just $1 } | '#' { Nothing }

optStrat :             { Longest } 
         | ',' strat   { $2 } 

strat : 'SHORTEST' { Shortest } | 'LONGEST' { Longest } | 'RANDOM' { Random }

-- configurations

tconf : optional('{') seq(expr) ents(tref) optional('}') {TConf $2 $3 }
pconf : optional('{') seq(pattern) ents(pref) optional('}') {PConf $2 $3 }

tref : ID '=' seq(expr)     { ($1,$3) }
pref : ID '=' seq(pattern)  { ($1,$3) }

ents(ref) : optional(entsAux(ref))          { maybe [] id $1 }
entsAux(ref) : ',' multipleSepBy1(ref,',')  { $2 }

-- transitions

tctxt    : optional(tctxtAux)             { maybe [] id $1 }
tctxtAux : multipleSepBy1(tref,',') '|-'  { $1 }
pctxt    : optional(pctxtAux)             { maybe [] id $1 }
pctxtAux : multipleSepBy1(pref,',') '|-'  { $1 }

concl : pctxt pconf RELSYMB tconf { Concl $1 $2 $3 $4 }
premise : tctxt tconf RELSYMB pconf { Prem $1 $2 $3 $4 }

-- rules
sidecon : seq(expr) optional(sideconAux)  
                    { SideOP $1 (maybe [PVal (VOP.tobool True)] id $2) }
        | 'is-terminal' conssetkey seq(expr) { Term $2 $3 }
        | 'is-non-terminal'  conssetkey seq(expr) { NonTerm $2 $3 }
sideconAux : '|>' seq(pattern)  { $2 }

conditions: '#' {[]} | multiple1(condition) { $1 }
condition : either(premise,sidecon) { $1 }

inference : conditions optional(parens(INT)) BAR concl vardecls
              { Rule (maybe user_priority id $2) $4 $1 $5 }

-- basics

id  : ID  { $1 }
var : optional('_') ALT { (maybe "" (const "_") $1) ++ $2 }
rsymb : RELSYMB optional('*') { case $2 of {Just _ -> mRel $1; Nothing -> sRel $1} }
conssetkey : RELSYMB { $1 } | eid { $1 }
eid : ID { $1 }
opname : '_' ID { $2 }

expr : term { ETerm $1 }
     | opname optional(multipleSepBy(expr,',')) { VOP $1 (maybe [] id $2) }

term : var { TVar $1 }
     | id optional(parens(multipleSepBy(term,','))) { TCons $1 (maybe [] id $2) }
     | literal(term)  { TVal $1 }

pattern : var { PVar $1 }
        | '?' { PAny }
        | '_' { PAny }
        | id optional(parens(multipleSepBy(pattern,','))) { PCons $1 (maybe [] id $2) }
        | literal(pattern) { PVal $1 }

literal(p) : id angles(multipleSepBy(p,',')) { VOP.ADTVal (pack $1) $2 }
           | id brackets(multipleSepBy(p,',')) { VOP.ComputationType (VOP.Type (VOP.ADT (pack $1) $2)) }
           | '-' INT { VOP.Int (toInteger (0-$2)) }
           | INT { VOP.Nat (toInteger $1) }
           | STRING { fromString $1 }
           | CHAR { VOP.mk_unicode_characters $1 }

-- reusable productions
parens(p)   : '(' p ')' { $2 } 
angles(p)   : '<' p '>' { $2 } 
brackets(p) : '[' p ']' { $2 } 

seq(p) : '#' { [] }
       | p optional(seqAux(p)) { maybe [$1] ($1:) $2 }
seqAux(p) : ',' multipleSepBy1(p,',') { $2 }

multiple(p) :                { [] }
            | p multiple(p)  { $1 : $2 }

multiple1(p) : p multiple(p) { $1 : $2 }

multipleSepBy(p,c) :                        { [] }
                   | p c multipleSepBy(p,c) { $1 : $3 }

multipleSepBy1(p,c) : p                      { [$1] }
                    | p c multipleSepBy(p,c) { $1 : $3 }

optional(p) :     { Nothing }
            | p   { Just $1 }

either(l,r) : l   { Left $1 }
            | r   { Right $1 }

{
parser = component_ happy_parser
}
