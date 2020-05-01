{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

module IML.Printer where

import Prelude hiding ((<>))

import IML.Grammar.Shared hiding (Spec(..))
import IML.Grammar
import IML.Grammar.Mixed
import IML.Grammar.Programs
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Trans.Unmix
import IML.Trans.ProMan
import IML.Trans.RemoveRO
import IML.Trans.RelFlags
import IML.Trans.WrapSpec
import IML.CodeGen.Shared hiding (repHyphen)
import qualified IML.CodeGen.Shared as UTIL

import Funcons.Operations (ppValues)
import qualified Funcons.Operations as VOP 

import Control.Arrow ((>>>))
import Data.List (intersperse)
import Data.Set (toList) 
import Text.PrettyPrint.HughesPJ hiding (bracketed)
import Data.Text (unpack)


program2string:: Component MixedProgram String 
program2string = 
  rules_from_flags >>> remove_read_only >>> unmix >>> component iml_print

program2highstring :: Component MixedProgram String
program2highstring =
  rules_from_flags >>> remove_read_only >>> component iml_mixed_print

spec2string:: Component HighSpec String 
spec2string = mix_spec >>> wrap_spec >>>  
  rules_from_flags >>> remove_read_only >>> unmix >>> component iml_print

spec2highstring :: Component HighSpec String
spec2highstring = mix_spec >>> wrap_spec >>>
  rules_from_flags >>> remove_read_only >>> component iml_mixed_print

iml_mixed_print :: MixedProgram -> ProMan String
iml_mixed_print (Program spec qs) = do
  doRep <- boolOpt opt_no_hyphen 
  let ?repHyphen = if doRep then UTIL.repHyphen else id
  return (render $  
     ppInteractions qs $+$ text "" $+$ ppMixedSpec spec)

iml_print :: Program -> ProMan String
iml_print pr = do 
  doRep <- boolOpt opt_no_hyphen
  let ?repHyphen = if doRep then UTIL.repHyphen else id
  return $ render $ ppProgram pr

ppProgram :: (?repHyphen :: String -> String) => Program -> Doc
ppProgram (Program spec qs) = 
  ppInteractions qs $+$ text "" $+$ ppSpec spec

ppMixedSpec :: (?repHyphen :: String -> String) => MixedSpec -> Doc
ppMixedSpec (Spec ds) = vcat $ 
  map (withDecl ppEntDecl ppTConsDecl ppRelDecl ppVarDecl (ppEither ppRule ppProcDecl)) ds

ppSpec :: (?repHyphen :: String -> String) => LowSpec -> Doc
ppSpec (Spec ds) = vcat $ intersperse (text "") $
  map (withDecl ppEntDecl ppTConsDecl ppRelDecl ppVarDecl ppProcDecl) ds

ppVarDecl :: (?repHyphen :: String -> String) => VarDecl -> Doc
ppVarDecl (VarDecl var l mu strat conds) 
 | null conds = conclusion 
 | otherwise  = vcat (map ppCond conds) $+$ text "------" $+$ conclusion
  where conclusion = text "seq-variable" <> 
                        showArgs [gVar var, text (show l), upDoc, stratDoc]
        upDoc = maybe (text "#") (text . show) mu
        stratDoc = case strat of 
          Longest   -> text "LONGEST"
          Shortest  -> text "SHORTEST"
          Random    -> text "RANDOM"

ppRule :: (?repHyphen :: String -> String) => Rule -> Doc
ppRule (Rule prio concl conds vds) =
  conditions $+$
  showArgs [text (show prio)] <+> text "------" $+$
  ppConclusion concl $+$ ppVarDecls
  where conditions | null conds = text "#"
                   | otherwise  = vcat $ map ppCond conds
        ppVarDecls | null vds = empty
                   | otherwise = nest 2 (text "with" $+$ 
                                   nest 2 (vcat (map ppVarDecl vds)))

ppCond :: (?repHyphen :: String -> String) => Either Premise SideCon -> Doc
ppCond (Left prem) = ppPremise prem 
ppCond (Right sc)  = case sc of
  SideOP expr pat   -> ppSeq ppExpr expr <+> text "|>" <+> ppSeq ppPattern pat
  Term skey expr    -> text "is_terminal" <> showArgs [text skey, ppSeq ppExpr expr]
  NonTerm skey expr -> text "is_non_terminal" <> showArgs [text skey, ppSeq ppExpr expr]

ppConclusion :: (?repHyphen :: String -> String) => Conclusion -> Doc
ppConclusion (Concl ros pconf rel tconf) = 
  context <+> ppPConf pconf <+> ppRel rel <+> ppTConf tconf 
  where context | null ros  = empty
                | otherwise = ppEntAccs ros <+> text "|-"

ppEntAccs :: (?repHyphen :: String -> String) => [EntAcc] -> Doc
ppEntAccs = hcat . intersperse comma . map ppEntAcc

ppEntAcc :: (?repHyphen :: String -> String) => EntAcc -> Doc
ppEntAcc (eid, pat) = ppEid eid <=> ppSeq ppPattern pat 

ppEntUp :: (?repHyphen :: String -> String) => EntUp -> Doc
ppEntUp (eid, expr) = ppEid eid <=> ppSeq ppExpr expr

ppInteractions :: (?repHyphen :: String -> String) => [Interaction] -> Doc
ppInteractions = vcat . map ppInteraction

ppInteraction :: (?repHyphen :: String -> String) => Interaction -> Doc
ppInteraction (DoQuery q) = ppQuery q
ppInteraction (ResetEnv)  = text ">" <+> text "RESET-BINDINGS"

ppQuery :: (?repHyphen :: String -> String) => Query -> Doc
ppQuery (Query prem vds) = text ">" <+> ppPremise prem $+$ ppVarDecls
 where  ppVarDecls | null vds = empty
                   | otherwise = nest 2 (text "with" $+$ 
                                   nest 2 (vcat (map ppVarDecl vds)))

ppPremise :: (?repHyphen :: String -> String) => Premise -> Doc
ppPremise (Prem _ tc rel pc) = 
  ppTConf tc <+> ppRel rel <+> ppPConf pc

ppTConf :: (?repHyphen :: String -> String) => TConf -> Doc
ppTConf (TConf t []) = braces (ppSeq ppExpr t)
ppTConf (TConf t inhs) = braces $ hcat $ intersperse comma $ (ppSeq ppExpr t:) $
  map ppEntUp inhs

ppPConf :: (?repHyphen :: String -> String) => PConf -> Doc
ppPConf (PConf t []) = braces (ppSeq ppPattern t)
ppPConf (PConf t outs) = braces $ hcat $ intersperse comma $ (ppSeq ppPattern t:) $
  map ppEntAcc outs

ppEntDecl :: (?repHyphen :: String -> String) => EntDecl -> Doc
ppEntDecl (EntDecl eid expr) = 
  text "entity" <> showArgs [ppEid eid, ppSeq ppExpr expr]

ppTConsDecl :: (?repHyphen :: String -> String) => TConsDecl -> Doc
ppTConsDecl (PCTerm rsymb ebc) = text "terminal" <> 
  showArgs [text rsymb, ppEither (text . show) text ebc]
ppTConsDecl (EIDTerm eid ebc) = text "terminal" <>
  showArgs [ppEid eid, ppEither (text. show) text ebc]

ppRel :: RSymb -> Doc
ppRel r = text r

ppRelDecl :: RelDecl -> Doc
ppRelDecl (RelDecl rel preds) = 
  text "relation" <> showArgs (text rel : map (text . show) preds)

ppProcDecl :: (?repHyphen :: String -> String) => ProcDecl -> Doc
ppProcDecl (Proc prio sym mcons stmts) = 
    text "procedure" <> showArgs args <> text "{" $+$ 
    ppBranches 1 stmts
  where args = (text (show prio):) $ (text sym:) $ case mcons of 
                Left i    -> [text (show i)]
                Right sp  -> [ppSeq ppMCons sp]
        ppMCons (NoCons i j)= error "ppProcDecl"  --TODO
        ppMCons (TeCons cs) = ppCons cs
        ppMCons (TyCons cs) = ppCons cs <> "[]"
        ppMCons (VaCons cs) = ppCons cs <> "<>"

ppStmtsLine :: (?repHyphen :: String -> String) => Stmts -> Doc
ppStmtsLine = hcat . map (enclose . ppStmt)
  where enclose s = s <> semi

ppStmts :: (?repHyphen :: String -> String) => Stmts -> Doc
ppStmts = ppStmtsB 1  

ppStmtsB :: (?repHyphen :: String -> String) => Int -> Stmts -> Doc
ppStmtsB branchnr = vcat . map (ppStmtB branchnr)

ppStmt :: (?repHyphen :: String -> String) => Stmt -> Doc
ppStmt = ppStmtB 1

ppStmtB nro (Branches sss) = text "branches" <> text "{" $+$ ppBranches 1 sss 
ppStmtB nro s = ppStmtBSemi nro s <> semi

ppStmtBSemi :: (?repHyphen :: String -> String) => Int -> Stmt -> Doc
ppStmtBSemi branchnr s = case s of
--  Skip              -> text "skip"
--  Abort             -> text "aborts"
--  Assert e          -> text "assert" <> showArgs [ppExpr e]
  PM e p            -> text "pm" <> showArgs [ppParensSeq ppExpr e, ppParensSeq ppPattern p]
  IsTerm r t        -> text "is_terminal" <> showArgs [text r, ppSeq ppTerm t]
  IsNonTerm r t     -> text "is_non_terminal" <> showArgs [text r, ppSeq ppTerm t]
  Commit t Nothing  -> text "commit" <> showArgs [ppSeq ppTerm t]
  Commit t (Just si)-> text "commit" <> showArgs [ppSeq ppTerm t, ppStaticRuleInfo si]
  Trans rel t x ml  -> text "trans" <> showArgs [ppRel rel, ppParensSeq ppTerm t, ppParensSeq gVar x,ppLabel ml]
  Set eid e l       -> text "set" <> showArgs [ppEid eid, ppSeq ppTerm e, ppLabel l]
  Get eid x l       -> text "get" <> showArgs [ppEid eid, ppSeq gVar x, ppLabel l]
  where ppLabel i = text (show i) 


ppSeq = ppSeqAbs False
ppParensSeq = ppSeqAbs True
ppSeqAbs :: Bool -> (a -> Doc) -> [a] -> Doc
ppSeqAbs doParens pp []  = text "#"
ppSeqAbs doParens pp [a] = pp a
ppSeqAbs doParens pp as  = parens' $ hcat $ intersperse comma $ map pp as
  where parens' | doParens  = parens
                | otherwise = id

ppBranches :: (?repHyphen :: String -> String) => Int -> [Stmts] -> Doc
ppBranches branchnr sss = (if branchnr == 1 then empty else text "{") $+$ 
    branches $+$
  text "}"
  where branches = vcat $ intersperse (text "}{")
                                  (map (nest 4 . ppStmtsB (branchnr + 1)) sss)


ppExpr ::  (?repHyphen :: String -> String) => Expr -> Doc
ppExpr (ETerm t) = ppTerm t
ppExpr (VOP op es) 
  | null es = ppOp op
  | otherwise =  ppOp op <> showArgs (map ppExpr es)

ppTerm :: (?repHyphen :: String -> String) => Term -> Doc
ppTerm (TVar v) = gVar v
ppTerm (TVal v) = ppBuiltinLiteral (render . ppTerm) v
ppTerm (TCons cs ts)  | null ts   = ppCons cs
                      | otherwise = ppCons cs <> showArgs (map ppTerm ts)

ppBuiltinLiteral :: (?repHyphen :: String -> String, VOP.HasValues t) => (t -> String) -> VOP.Values t -> Doc
ppBuiltinLiteral showT v = case v of 
  v@(VOP.ADTVal _ _ ) | VOP.isString_ v -> doubleQuotes (text (VOP.unString v))
  VOP.ADTVal cs vs      -> text (?repHyphen (unpack cs)) <> angled (map (text . showT) vs)
  VOP.ComputationType (VOP.Type (VOP.ADT cs ts)) -> text (unpack cs) <> bracketed (map (text . showT) ts)
  -- strings, chars, integers, reuse `ppValues`
  _       -> text $ ppValues showT v 

ppPattern :: (?repHyphen :: String -> String) => Pattern -> Doc
ppPattern PAny                = text "_"
ppPattern (PVar v)            = gVar v
ppPattern (PCons cons ps)     = ppCons cons <> showArgs (map ppPattern ps)
ppPattern (PVal v)            = ppBuiltinLiteral (render . ppPattern) v

angled :: [Doc] -> Doc
angled docs = text "<" <> csd docs <> text ">"

bracketed :: [Doc] -> Doc
bracketed docs = text "[" <> csd docs <> text "]"


{-
ppVPattern :: Funcons.Operations.VPattern Term -> Doc
ppVPattern (VPMVar v)         = gVar v
ppVPattern (VPLit l)          = text $ ppValues l
ppVPattern (VPAny)            = text "_"
ppVPattern (VPADT cons ps) 
  | null ps   = text (unpack cons)
  | otherwise = text (unpack cons) <> showArgs (map ppVPattern ps)
-}

ppOp :: (?repHyphen :: String -> String) => String -> Doc
ppOp op = text "_" <> text (?repHyphen op)

ppEid :: (?repHyphen :: String -> String) => String -> Doc
ppEid eid = text (?repHyphen eid)

ppCons :: (?repHyphen :: String -> String) => String -> Doc
ppCons cs = text (?repHyphen (cs))

showArgs :: [Doc] -> Doc
showArgs args = lparen <> hcat (intersperse comma args) <> rparen

gVar :: MVar -> Doc
gVar v = text v

dquote = doubleQuotes . text

showResetBindings = showInteraction (ResetEnv)
  where ?repHyphen = id
showInteraction = render . ppInteraction
  where ?repHyphen = id
showQuery = render . ppQuery
  where ?repHyphen = id
showPattern = render . ppPattern
  where ?repHyphen = id
showTerm = render . ppTerm
  where ?repHyphen = id
showStmt = render. ppStmt
  where ?repHyphen = id
showRel  = render. ppRel

ppStaticRuleInfo :: (?repHyphen :: String -> String) => StaticRuleInfo -> Doc
ppStaticRuleInfo (SRI i ents) = parens $ hcat $ intersperse comma $ text (show i) : map ppEid ents
