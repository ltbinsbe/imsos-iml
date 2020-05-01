
module IML.CodeGen.LaTeX where

import Prelude hiding ((<>))

import IML.CodeGen.LaTeXModule
import IML.CodeGen.Shared
import IML.Grammar.Shared 
import IML.Grammar.High
import IML.Grammar.Mixed
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Trans.ProMan
import IML.Trans.RemoveRO
import IML.Trans.RelFlags
import IML.Trans.WrapSpec

import Funcons.Operations (Values(..),ComputationTypes(..),Types(..),ppValues, HasValues(..), isString_, unString, upcastCharacter)

import Control.Arrow ((>>>), (***))
import Data.Text (splitOn, pack, unpack)
import Data.Char (toLower,isAlpha,isDigit)
import Data.List (intersperse)
import Text.PrettyPrint.HughesPJ

program2latex_module :: Component MixedProgram LaTeXModule
program2latex_module = 
  rules_from_flags >>> remove_read_only >>> component_ gProgram

spec2latex_module :: Component HighSpec LaTeXModule
spec2latex_module = mix_spec >>> wrap_spec >>> 
  rules_from_flags >>> remove_read_only >>> component_ gProgram

gProgram :: MixedProgram -> LaTeXModule
gProgram pr@(Program (Spec decls) _) = defaultModule {
    lm_fragments  = zipWith (\i d -> (i, gAnyDecls d)) [1..] decls 
  }

gAnyDecls :: AnyDecls MixedDecl -> Doc
gAnyDecls (AnEntDecl e)         = gEntity e
gAnyDecls (ARuleDecl (Left r))  = gRule r  
gAnyDecls (ARuleDecl (Right r)) = empty
gAnyDecls (ATConsDecl t)        = gTermCons t
gAnyDecls (ARelDecl r)          = gRelation r
gAnyDecls (AVarDecl v)          = gVarDecl v

gTermCons :: TConsDecl -> Doc
gTermCons (PCTerm r cs) = 
  textbf "terminal" <> parens (textrsymb r <> comma <> gEither gBType mathit cs) 
gTermCons (EIDTerm eid cs) = 
  textbf "terminal" <> parens (textsf eid <> comma <> gEither gBType mathit cs)

gBType :: BuiltinType -> Doc
gBType = text . show
 
gEntity :: EntDecl -> Doc
gEntity (EntDecl eid expr) = 
  textbf "entity" <> parens (textsf eid <> comma <> gSeq id gExpr expr)

gRelation :: RelDecl -> Doc
gRelation (RelDecl rsym flags) = 
  textbf "relation" <> parens (textrsymb rsym <> optcomma <> gFlags) 
  where gFlags = hcat $ intersperse comma $ map (textsc . show) flags
        optcomma | null flags = empty
                 | otherwise  = comma

gVarDecl :: VarDecl -> Doc
gVarDecl (VarDecl var lb mup strat conds) = 
  frac (gConditions conds)
       (textbf "seq-variable" <> gTuple [tvar var, text (show lb), ubDoc, stratDoc]) Nothing 
  where ubDoc = maybe (text "\\infty") (text . show) mup 
        stratDoc = case strat of 
          Longest   -> textsc "LONGEST"
          Shortest  -> textsc "SHORTEST"
          Random    -> textsc "RANDOM"

gRule :: Rule -> Doc
gRule r@(Rule prio concl conds _) = 
  frac (gConditions conds) (gConclusion concl) (Just prio)
  where 
    gConclusion (Concl ros (PConf p ins) r (TConf t outs)) = 
      gContext gPattern ros 
            <+> gConfiguration (gSeq id gPattern p) (map (textsf *** (gSeq id gPattern)) ins)
            <+> gRel r 
            <+> gConfiguration (gSeq id gExpr t) (map (textsf *** (gSeq id gExpr)) outs)

gConditions :: [Either Premise SideCon] -> Doc   
gConditions = hsep . intersperse (text "\\\\") . map gCondition

gCondition :: Either Premise SideCon -> Doc
gCondition (Right (SideOP expr pat)) = 
  gSeq id gExpr expr <+> text "\\triangleright" <+> gSeq id gPattern pat
gCondition (Right (Term rsymb cs)) =
  textbf "is-terminal" <--> braces (textrsymb rsymb) <> parens (gSeq id gExpr cs)
gCondition (Right (NonTerm rsymb cs)) =
  textbf "is-non-terminal" <--> braces (textrsymb rsymb) <> parens (gSeq id gExpr cs)
gCondition (Left (Prem ros (TConf t ins) rel (PConf p outs))) = 
  gContext gExpr ros 
      <+> gConfiguration (gSeq id gExpr t) (map (textsf *** (gSeq id gExpr)) ins)
      <+> gRel rel 
      <+> gConfiguration (gSeq id gPattern p) (map (textsf *** (gSeq id gPattern)) outs)

gConfiguration :: Doc -> [(Doc, Doc)] -> Doc
gConfiguration term [] = text "\\{" <> term <> text "\\}"
gConfiguration term aux = 
      text "\\{" <+> term <+> comma <+> csd (map pair aux) <+> text "\\}"
      where pair (eid,term) = eid <=> term 

gContext gVal ros
  | null ros  = empty
  | otherwise = ( hsep $ intersperse comma $ 
                  [ textsf ent <+> equals <+> gSeq id gVal t
                  | (ent,t) <- ros ] ) <+> turnstile



gEither :: (a -> Doc) -> (b -> Doc) -> Either a b -> Doc
gEither f g (Left a) = f a
gEither f g (Right b) = g b

gExpr :: Expr -> Doc
gExpr e = case e of 
  ETerm t       -> gTerm t
  VOP op es 
    | null es   -> gOP op
    | otherwise -> gOP op <> parens (hsep $ intersperse comma $ map gExpr es)

gOP :: VOP -> Doc
gOP op = texttt op

gRel :: RSymb -> Doc
gRel rsymb = textrsymb rsymb

gTerm :: Term -> Doc
gTerm t = case t of
  TVar x -> tvar x
  TVal v -> ppLit gTerm v
  TCons nm ts | null ts  -> mathit nm
              | otherwise-> mathit nm <> gTuple (map gTerm ts) 

ppLit :: HasValues t => (t -> Doc) -> Values t -> Doc
ppLit gterm v = case v of 
  Int i             -> text (show i)
  v | isString_ v   -> text "``" <> mathtext (unString v) <> text "\""
  v | Just c <- upcastCharacter v -> quotes (text (show c))
  ADTVal nm vs      -> mathit (unpack nm) <> angled (map gterm vs)
  ComputationType (Type (ADT nm ts))
                    -> mathit (unpack nm) <> bracketed (map gterm ts)
  _                 -> text (ppValues (render . gterm) v)


gPattern :: Pattern -> Doc
gPattern p = case p of
  PAny          -> text "\\_"
  PVal vp       -> ppLit gPattern vp
  PVar x        -> tvar x
  PCons cs ps | null ps     -> mathit cs
              | otherwise   -> mathit cs <> gTuple (map gPattern ps)

angled :: [Doc] -> Doc
angled docs = text "\\langle" <> csd docs <> text "\\rangle"

bracketed :: [Doc] -> Doc
bracketed docs = brackets (csd docs)

textsf :: String -> Doc
textsf = (text "\\textsf" <>) . braces . text . escUnderscore
textsc :: String -> Doc
textsc = (text "\\textsc" <>) . braces . text . map toLower . escUnderscore 


texttt :: String -> Doc
texttt = (text "\\texttt" <>) . braces . text . escUnderscore


mathit :: String -> Doc
mathit = hcat . intersperse (text "\\text{-}") . 
          map ((text "\\mathit" <>) . braces . text . unpack) . 
          splitOn (pack "-") . pack . escUnderscore 

mathtext :: String -> Doc
mathtext = (text "\\text" <>) . braces . text . escUnderscore

textbf = (text "\\textbf" <>) . braces . text . escUnderscore

frac :: Doc -> Doc -> Maybe Int -> Doc
frac top bot mprio = text "\\inferrule*" <> gPrioDoc <> braces top <> braces bot
  where gPrioDoc | Just prio <- mprio = brackets $ text "right" <=> text "\\scriptsize prio:" <> gPrio prio
                 | otherwise = empty
        gPrio = text . show 

tvar :: String -> Doc
tvar xs@(x:rst) 
  | x == '_'      = text "\\underline" <> braces (tvar rst)
  | not (null indexRev) 
                  = tvar (reverse restRev) <> text "_" 
                     <> braces (text (reverse indexRev))
  | lst == '*'    = tvar int <> text "^*"
  | lst == '+'    = tvar int <> text "^+"
  | lst == '?'    = tvar int <> text "^?"
  | lst == '\''   = tvar int <> text "'"
  | otherwise     = pvar xs
  where lst = last xs
        int = init xs
        (indexRev, restRev) = span isDigit (reverse xs)
tvar []           = text "?"

pvar :: String -> Doc
pvar "Sig" = text "\\sigma"
pvar "Rho" = text "\\rho"
pvar "Alp" = text "\\alpha"
pvar "Bet" = text "\\beta"
pvar "Gam" = text "\\gamma"
pvar xs    = mathit xs
  
textrsymb :: RSymb -> Doc
textrsymb "->"    = text "\\rightarrow"
textrsymb "->*"   = text "\\rightarrow^*"
textrsymb "~>"    = text "\\rightsquigarrow"
textrsymb "~>*"   = text "\\rightsquigarrow^*"
textrsymb "->>"   = text "\\twoheadrightarrow"
textrsymb "=>"    = text "\\Rightarrow"
textrsymb "=>*"   = text "\\Rightarrow^*"
textrsymb "=~="   = text "\\simeq"
textrsymb comp 
  | length comp <= 2 = text comp 
  | all isAlpha mid, length comp > 3 = 
    case (head comp, last (init comp), last comp) of
      ('-','-','>')   -> text "\\rightarrow_" <> braces (text "\\!" <> mathit (map toLower mid))
      ('=','=','>')   -> text "\\Rightarrow_" <> braces (text "\\!" <> mathit (map toLower mid))
      _               -> text comp
  | otherwise       = text comp
 where mid = init (init (tail comp))

turnstile :: Doc
turnstile = text "\\vdash"
