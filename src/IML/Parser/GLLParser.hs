{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module IML.Parser.GLLParser where

import IML.Grammar.Shared as Shared
import IML.Grammar.High
import IML.Grammar.Mixed
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Trans.ProMan
import IML.Parser.Shared

import qualified Funcons.Operations as VOP
import GLL.Combinators
import Data.Text (pack)
import Data.String (fromString)

type Parser a = BNF Token a

parser :: Component [Token] MixedProgram
parser = component_ iml_parse

iml_parse :: [Token] -> MixedProgram
iml_parse = head . iml_parser

iml_parser :: [Token] -> [MixedProgram]
iml_parser inp = case parseWithOptions [throwErrors] pProgram inp of
  []  -> error "no parse errors, but no result?"
  ps  -> ps

pProgram :: Parser MixedProgram
pProgram = "PROGRAM" <:=> mkProgram <$$> multiple pFragment

pFragment :: Parser Fragment
pFragment = "DECL"
  <:=  FRelation <$$ keyword "relation" <**> parens pRelDecl
  <||> FEntity <$$ keyword "entity" <**> parens pEntDecl
  <||> FTermCons<$$ keyword "terminal" <**> parens pTConsDecl
  <||> FRule <$$> pInference
  <||> FProc <$$> pProc
  <||> FQuery <$$> pQuery
  <||> FResetEnv <$$ keychar '>' <** keyword "RESET-BINDINGS"

-- keychar '>' prevents an ambiguity here
-- otherwise Term => Pattern may be interpreted as a premise and vice-versa
pQuery :: Parser Query
pQuery = "QUERY" <:=> Query <$$ keychar '>' <**> pPremise <**> pVarDecls

pEntDecl :: Parser EntDecl
pEntDecl = "ENT-DECL" <:=> EntDecl <$$> id_lit <** keychar ',' <**> pSeq pExpr

pEID :: Parser EID
pEID = "EID" <:=> id_lit

pTConsDecl :: Parser TConsDecl
pTConsDecl = "TCONS-DECL"
  <:=> PCTerm   <$$> pRSymb <** keychar ',' <**> pEither pBuiltinType pId
  <||> EIDTerm  <$$> id_lit <** keychar ',' <**> pEither pBuiltinType pId
  where pBuiltinType = "BUILTIN-TYPE"
          <:=> Booleans   <$$ keyword "BOOLEANS"
          <||> Atoms      <$$ keyword "ATOMS"
          <||> Values     <$$ keyword "VALUES"
          <||> Maps       <$$ keyword "MAPS"
          <||> Strings    <$$ keyword "STRINGS"
          <||> Integers   <$$ keyword "INTEGERS"
          <||> Characters <$$ keyword "CHARACTERS"
          <||> Lists      <$$ keyword "LISTS"
          <||> Sets       <$$ keyword "SETS"
          <||> Tuples     <$$ keyword "TUPLES"
          <||> Types      <$$ keyword "TYPES"
          <||> ADTs       <$$ keyword "ADTS"

pRelDecl :: Parser RelDecl
pRelDecl = "REL-DECL" <:=> RelDecl <$$> pRSymb <**> mProps
  where mProps = maybe [] id <$$>
                  optional (keychar ',' **> multipleSepBy1 pProp (keychar ','))
        pProp = "REL-PROP"
          <:=> IsPure <$$ keyword "CONTEXT-FREE"
          <||> IsPure <$$ keyword "CONTEXT_FREE"
          <||> Reflexive <$$ keyword "REFLEXIVE"
          <||> Repeatable <$$ keyword "REPEATABLE"
          <||> HasValueOps <$$ keyword "VALUE-OPERATIONS"
          <||> HasValueOps <$$ keyword "VALUE_OPERATIONS"

pVarDecls :: Parser [VarDecl]
pVarDecls = "LOCAL-VAR-DECLS"
    <:=> satisfy []
    <||> keyword "with" **> multiple1 pVarDecl

pVarDecl :: Parser VarDecl
pVarDecl = "VAR-DECL" <:=>
  flip ($) <$$> pConditions <** keyword "seq-variable" <**> pVarConclusion
  where pVarConclusion :: Parser ([Either Premise SideCon] -> VarDecl)
        pVarConclusion = "VAR-CONCL"
          <:=> parens (VarDecl  <$$> pVar <**
                                    keychar ',' <**> int_lit <**
                                    keychar ',' <**> pMaxBound <**>
                                    optionalWithDef (keychar ',' **> pStrat) Longest)
          <||> parens (vardecl3 <$$> pVar <**
                                    keychar ',' <**> int_lit <**>
                                    optionalWithDef (keychar ',' **> pStrat) Longest)
          <||> parens (vardecl2 <$$> pVar <**>
                                    optionalWithDef (keychar ',' **> pStrat) Longest)
          where vardecl3 x l s = VarDecl x l Nothing s
                vardecl2 x s   = VarDecl x 0 Nothing s
        pMaxBound = "VAR-UP-BOUND" <:=> Just <$$> int_lit <||> Nothing <$$ keychar '#'
        pStrat = "VAR-AMBIG-STRAT" <:=> Shortest <$$ keyword "SHORTEST"
                                   <||> Longest  <$$ keyword "LONGEST"
                                   <||> Random   <$$ keyword "RANDOM"

        pConditions :: Parser [Either Premise SideCon]
        pConditions = "VAR-CONDS"
          <:=> multiple1 (pEither pPremise pSideCon) <** token "BAR"
          <||> satisfy []

pProc :: Parser ProcDecl
pProc = "PROCEDURE"
  <:=> ($) <$$ keyword "procedure" <**> parens
                (Proc <$$> optionalWithDef (int_lit <** keychar ',') user_priority
                      <**> pRSymb <** keychar ',' <**> (toEither <$$> pStaticPatterns))
           <**> multiple1 pBranch
  where toEither [NoCons i _] = Left i
        toEither ps           = Right ps

pStaticPatterns :: Parser [StaticPattern]
pStaticPatterns = "STATIC-PATTERNS"
  <:=> multipleSepBy1 pStaticPattern (keychar ',')

pStaticPattern :: Parser StaticPattern
pStaticPattern = "STATIC-PATTERN"
  <:=> mkSPat <$$> pEither id_lit int_lit <**> optional conser
  where conser =      brackets (satisfy TyCons)
                 <||> angles (satisfy VaCons)
        mkSPat (Right i) _            = NoCons i (error "pStaticPattern") --TODO
        mkSPat (Left cs) Nothing      = TeCons cs
        mkSPat (Left cs) (Just cons)  = cons cs

pBranch :: Parser Stmts
pBranch = "BRANCH" <:=> braces pStmts

pStmts :: Parser Stmts
pStmts = "BODY" <:=>
  optional (keychar '|') **> multipleSepBy pStmt (optional (keychar '|'))

pStmt :: Parser Stmt
pStmt = "STMT" <:=> pStmtAlt <** optional (keychar ';')
  where pStmtAlt :: Parser Stmt
        pStmtAlt = "ALT-STMT"
          <:=> Branches <$$ keyword "branches" <**> multiple1 pBranch
          <||> binary "pm" PM (pParensSeq pExpr) (pParensSeq pPattern)
          <||> binary "is-terminal" IsTerm pConsSetKey (pSeq pTerm)
          <||> binary "is_terminal" IsTerm pConsSetKey (pSeq pTerm)
          <||> binary "is-non-terminal" IsNonTerm pRSymb (pSeq pTerm)
          <||> binary "is_non_terminal" IsNonTerm pRSymb (pSeq pTerm)
          <||> ternary_ "trans" Trans pRSymb (pParensSeq pTerm) (pParensSeq pVar)
          <||> binary_ "get" Get pId (pSeq pVar)
          <||> binary_ "set" Set pId (pSeq pTerm)
          <||> unary "commit" (flip Commit Nothing) (pSeq pTerm)
          <||> binary "commit" (\x y -> Commit x Nothing) (pSeq pTerm) (parens pStaticRuleInfo)

pId :: Parser String
pId = "NO-HYPHEN-ID" <:=> id_lit

pExpr :: Parser Expr
pExpr = "EXPR"
  <::=> ETerm <$$> pTerm
  <||>  VOP <$$> pOpName <**>
          optionalWithDef (parens (multipleSepBy pExpr (keychar ','))) []

pTerm :: Parser Term
pTerm = "TERM"
  <::= TVar <$$> pVar
  <||> flip ($) <$$> id_lit <**> pContTerm
  <||> TVal <$$> pBuiltinLiteral
  where pContTerm :: Parser (String -> Term)
        pContTerm = "CONT-TERM"
          <:=> flip TCons <$$> optionalWithDef (parens
                               (multipleSepBy pTerm (keychar ','))) []
          <||> adtval <$$> angles (multipleSepBy pTerm (keychar ','))
          <||> adt <$$> brackets (multipleSepBy pTerm (keychar ','))
          where adtval ts nm = TVal (VOP.ADTVal (pack nm) ts)
                adt ts nm = TVal (VOP.ComputationType (VOP.Type (VOP.ADT (pack nm) ts)))

pBuiltinLiteral :: VOP.HasValues t => Parser (VOP.Values t)
pBuiltinLiteral = "BUILTIN"
  <::= VOP.Int . toInteger. (0-) <$$ keychar '-' <**> int_lit
  <||> VOP.Nat . toInteger <$$> int_lit
  <||> fromString <$$> string_lit
  <||> VOP.mk_unicode_characters <$$> char_lit

pPattern :: Parser Pattern
pPattern = "Pattern"
  <::=  PAny <$$ keychar '_'
  <||> PAny <$$ keychar '?'
  <||> PVar <$$> pVar
  <||> flip ($) <$$> id_lit <**> pCont
  <||> PVal <$$> pBuiltinLiteral
  where pCont :: Parser (String -> Pattern)
        pCont = "CONT-PATTERN"
          <:=> flip PCons <$$> optionalWithDef (parens
                                (multipleSepBy pPattern (keychar ','))) []
          <||> adtval <$$> angles (multipleSepBy pPattern (keychar ','))
          <||> adt <$$> brackets (multipleSepBy pPattern (keychar ','))
          where adtval ts nm = PVal (VOP.ADTVal (pack nm) ts)
                adt ts nm = PVal (VOP.ComputationType (VOP.Type (VOP.ADT (pack nm) ts)))



pVar :: Parser MVar
pVar = "MVAR"
  <:=> tvar <$$> optional (keychar '_') <**> alt_id_lit
  <||> keyword prebound_mvar
  where tvar mus alt = (maybe "" (:[]) mus) ++ alt
{-
pMVar :: Parser MVar
pMVar = pVar id

pVar :: (MVar -> a) -> Parser a
pVar cons = "MVAR" <:=> tvar <$$> optional (keychar '_') <**> alt_id_lit
                            <**> optional ranges
  where tvar m_ altid mr = cons $ MVar var l u
          where var   = maybe altid (const ('_':altid)) m_
                (l,u) = maybe (1,Just 1) id mr
        ranges = "RANGES-MVAR" <:=> (,) <$$
                    keychar '_' <**> int_lit <** keychar '_' <**> maxrange
          where maxrange = "MAX-RANGES-MVAR" <:=> Nothing <$$ keychar '*'
                                           <||> Just <$$> int_lit
-}

pRSymb :: Parser RSymb
pRSymb = "REL" <:=> rel <$$> pRSymbSimple <**> pRep
  where rel s Nothing   = sRel s
        rel s (Just _)  = mRel s
        pRep = optional (keychar '*')

        pRSymbSimple :: Parser RSymb
        pRSymbSimple = token "REL-SYMB"

pConsSetKey :: Parser ConsSetKey
pConsSetKey = "CONS-SET-KEY" <:=> pRSymb <||> pEID

pOpName :: Parser VOP
pOpName = "VOP" <:=> keychar '_' **> id_lit

optsemi :: Parser (Maybe Char)
optsemi = "OPTIONAL-SEMI" <:=> optional (keychar ';')

unary :: String -> (a -> b) -> Parser a -> Parser b
unary key f p = mkRule $ f <$$ keyword key <**> parens p

binary :: String -> (a -> b -> c) -> Parser a -> Parser b -> Parser c
binary key f p1 p2 = mkRule (keyword key **> parens args)
  where args = mkRule $ f <$$> p1 <** keychar ',' <**> p2

ternary :: String -> (a -> b -> c -> d) ->
            Parser a -> Parser b -> Parser c -> Parser d
ternary key f p1 p2 p3 = mkRule (keyword key **> parens args)
  where args = mkRule $ f <$$> p1 <** keychar ',' <**> p2 <** keychar ',' <**> p3

quaternary :: String -> (a -> b -> c -> d -> e) ->
                Parser a -> Parser b -> Parser c -> Parser d -> Parser e
quaternary key f p1 p2 p3 p4 = mkRule $ keyword key **> parens args
  where args = mkRule $ f <$$> p1 <** keychar ','
                          <**> p2 <** keychar ','
                          <**> p3 <** keychar ','
                          <**> p4

arbitrary :: String -> ([a] -> b) -> Parser a -> Parser b
arbitrary key f p1 = mkRule $ keyword key **> parens args
  where args = mkRule $ f <$$> multipleSepBy p1 (keychar ',')

binary_ :: String -> (a -> b -> Label -> c) -> Parser a -> Parser b -> Parser c
binary_ key f p1 p2 = mkRule (keyword key **> parens args)
  where args = mkRule $ f <$$> p1 <** keychar ',' <**> p2
                          <** keychar ',' <**> int_lit

ternary_ :: String -> (a -> b -> c -> Label -> d) ->
            Parser a -> Parser b -> Parser c -> Parser d
ternary_ key f p1 p2 p3 = mkRule (keyword key **> parens args)
  where args = mkRule $ f <$$> p1 <** keychar ',' <**> p2 <** keychar ',' <**> p3
                          <** keychar ',' <**> int_lit

pEither :: Parser a -> Parser b -> Parser (Either a b)
pEither p1 p2 = mkRule $ Left <$$> p1 <||> Right <$$> p2

pTConf :: Parser TConf
pTConf = "TCONF" <:=> TConf
        <$$   optional (keychar '{')
        <**>  pSeq pExpr
        <**>  optionalWithDef (keychar ',' **> multipleSepBy1 pTRef (keychar ',')) []
        <**   optional (keychar '}')

pPConf :: Parser PConf
pPConf = "PCONF" <:=> PConf
        <$$   optional (keychar '{')
        <**>  pSeq pPattern
        <**>  optionalWithDef (keychar ',' **> multipleSepBy1 pPRef (keychar ',')) []
        <**   optional (keychar '}')

pTRef :: Parser EntUp
pTRef = "TRef"
  <:=> (,) <$$> id_lit <**  keychar '=' <**> pSeq pExpr

pPRef :: Parser EntAcc
pPRef = "PRef"
  <:=> (,) <$$> id_lit <**  keychar '=' <**> pSeq pPattern

pTCtxt :: Parser [RoUp]
pTCtxt = "TCtxt"
  <:=> optionalWithDef (multipleSepBy1 pTRef (keychar ',') <** keyword "|-") []
  where pTRef = "RO-TRef"
          <:=> (,) <$$> id_lit <**> parens (pSeq pExpr)
          <||> (,) <$$> id_lit <**  keychar '=' <**> pSeq pExpr


pPCtxt :: Parser [EntAcc]
pPCtxt = "PCtxt"
  <:=> optionalWithDef (multipleSepBy1 pPRef (keychar ',') <** keyword "|-") []

pInference :: Parser Rule
pInference = "INFERENCE"
  <:=> rule <$$> pConditions <**> optionalWithDef (parens int_lit) user_priority
                  <** token "BAR" <**> pConclusion <**> pVarDecls
 where
  rule cs prio cl = Rule prio cl cs
  pConditions :: Parser [Either Premise SideCon]
  pConditions = "CONDS" <:=> [] <$$ keychar '#'
                        <||> multiple1 (pEither pPremise pSideCon)

pSideCon :: Parser SideCon
pSideCon = "SIDE"
  <:=> SideOP <$$> pSeq pExpr <**>
         optionalWithDef (keyword "|>" **> pSeq pPattern) [PVal (VOP.tobool True)]
  <||> binary "is-terminal" Term pConsSetKey (pSeq pExpr)
  <||> binary "is_terminal" Term pConsSetKey (pSeq pExpr)
  <||> binary "is-non-terminal" NonTerm pConsSetKey (pSeq pExpr)
  <||> binary "is_non_terminal" NonTerm pConsSetKey (pSeq pExpr)

pSeq :: Parser a -> Parser [a]
pSeq p = mkNt p "SEQ-OF"
  <:=> merge <$$> p <**> optional (keychar ',' **> multipleSepBy1 p (keychar ','))
  <||> [] <$$ keychar '#'
  where merge e1 Nothing = [e1]
        merge e1 (Just es) = e1:es

pParensSeq :: Parser a -> Parser [a]
pParensSeq p = mkNt p "PARENS-SEQ"
  <:=> (:[]) <$$> p
  <||> parens (multipleSepBy2 p (keychar ','))
  <||> [] <$$ keychar '#'

pConclusion :: Parser Conclusion
pConclusion = "CONCLUSION" <:=> Concl <$$> pPCtxt <**> pPConf <**> pRSymb <**> pTConf

pPremise :: Parser Premise
pPremise = "PREMISE" <:=> Prem <$$> pTCtxt <**> pTConf <**> pRSymb <**> pPConf

pStaticRuleInfo :: Parser StaticRuleInfo
pStaticRuleInfo = "STATIC-RULE-INFO"
  <:=> SRI <$$> int_lit <**> optionalWithDef
                (keychar ',' **> multipleSepBy pEID (keychar ',')) []

{-
pRWEntAcc = Parser (EID, Pattern, Expr)
pRWEntAcc= "RW-ACC" <:=> (,,) <$$> id_lit <**> pPattern <**> pExpr

pRWEntUp = Parser (EID, Pattern, Expr)
pRWEntUp= "RW-UP" <:=> (,,) <$$> id_lit <**> pExpr <**> pPattern
-}


{-
-- | Flag value constructors in terms
class HasCons a where
  blossom :: [Cons] -> a -> a

instance HasCons a => HasCons [a] where
  blossom cs xs = map (blossom cs) xs

instance HasCons Query where
  blossom cs (Query t r p) = Query (blossom cs t) r (blossom cs p)

instance HasCons a => HasCons (AnyDecls a) where
  blossom cs ad = case ad of
    AnEntDecl d   -> AnEntDecl $ blossom cs d
    ARelDecl _    -> ad
    ARuleDecl a   -> ARuleDecl (blossom cs a)

instance HasCons EntDecl where
  blossom cs decl = case decl of
    RODecl eid e -> RODecl eid (blossom cs e)
    RWDecl eid e -> RWDecl eid (blossom cs e)
    WODecl eid f1 f2 -> WODecl eid f1 f2

instance (HasCons a, HasCons b) => HasCons (Either a b) where
  blossom cs (Left l) = Left (blossom cs l)
  blossom cs (Right r) = Right (blossom cs r)

instance HasCons a => HasCons (ATransDecl a) where
  blossom cs (Trans r f ss) = Trans r (blossom cs f) (blossom cs ss)

instance HasCons Rule where
  blossom cs (Rule (Conclusion f r t ros rws wos) es) =
    Rule (Conclusion (blossom cs f) r (blossom cs t) (blossom cs ros)
            (blossom cs rws) (blossom cs wos)) (blossom cs es)

instance HasCons SideCon where
  blossom cs (SideOP expr pat) = SideOP (blossom cs expr) (blossom cs pat)

instance HasCons Expr where
  blossom cs e = case e of
    ETerm t -> ETerm $ blossom cs t
    VOP op es -> VOP op $ blossom cs es

instance HasCons Premise where
  blossom cs (Prem t r p ros rws wos) =
    Prem (blossom cs t) r (blossom cs p) (blossom cs ros)
            (blossom cs rws) (blossom cs wos)

instance (HasCons a, HasCons b) => HasCons (a,b) where
  blossom cs (a,b) = (blossom cs a, blossom cs b)

instance (HasCons a, HasCons b, HasCons c) => HasCons (a,b,c) where
  blossom cs (a,b,c) = (blossom cs a, blossom cs b, blossom cs c)

instance HasCons Char where
  blossom cs = id

instance HasCons Pattern where
  blossom cs p = case p of
    PCons nm args -> PCons nm (blossom cs args)
    _             -> p

instance HasCons Term where
  blossom cs t = case t of
    TCons orig nm args  -> TCons (nm `elem` cs || orig) nm (blossom cs args)
    _                   -> t

instance HasCons Stmt where
  blossom cs stmt = case stmt of
    Commit t          -> Commit (blossom cs t)
    Branches sss      -> Branches (blossom cs sss)
    PM e p            -> PM (blossom cs e) p
    Unobserv l        -> Unobserv l
    Single r t x l    -> Single r (blossom cs t) x l
    Many r t x l      -> Many r (blossom cs t) x l
    RO_Get eid x      -> RO_Get eid x
    WO_Get eid x l    -> WO_Get eid x l
    RW_Get eid x l    -> RW_Get eid x l
    RO_Set eid e l    -> RO_Set eid (blossom cs e) l
    WO_Set eid e      -> WO_Set eid (blossom cs e)
    RW_Set eid e l    -> RW_Set eid (blossom cs e) l
-}
