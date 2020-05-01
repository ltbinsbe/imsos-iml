{-# LANGUAGE OverloadedStrings #-}

module IML.CodeGen.RascalModule where

import Prelude hiding ((<>))

import IML.CodeGen.Shared
import IML.Grammar.Shared 
import IML.Grammar.High
import IML.Grammar.Mixed
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Trans.ProMan
import IML.Trans.RemoveRO
import IML.Trans.RelFlags

import Funcons.Operations (Values(..),ComputationTypes(..),Types(..),ppValues, HasValues(..), isString_, unString, upcastCharacter)

import Control.Arrow ((>>>))

import Data.Function (on)
import Data.List (intersperse, isPrefixOf, sortBy)
import Data.Either (lefts)
import qualified Data.Map as M
import qualified Data.Set as S

import Text.PrettyPrint.HughesPJ


data Module = Module {
        module_name :: String
      , imports     :: [String]
      , components  :: [Doc] 
      }

data Config = Config {
        cfg_module_name :: Maybe String
      , cfg_imports     :: [String]
      }

mkConfig :: [String] -> Config
mkConfig [] = Config Nothing []
mkConfig (opt:rest) 
  | "--module-name=" `isPrefixOf` opt = (mkConfig rest)
    { cfg_module_name = Just (drop (length ("--module-name="::String)) opt) }
  | "--import=" `isPrefixOf` opt = 
    let cfg = mkConfig rest
    in cfg { cfg_imports = drop (length ("--import="::String)) opt : cfg_imports cfg  }
  | otherwise = mkConfig rest

applyConfig :: Config -> Module -> Module
applyConfig cfg mod' = mod'  {
    module_name = maybe (module_name mod') id (cfg_module_name cfg)
  , imports     = imports mod' ++ cfg_imports cfg
  }

gModule :: Module -> Doc
gModule mod = 
  text "module" <+> text (module_name mod) $+$
  text "" $+$
  vcat (map (\s -> text "import" <+> text s <> semi) (imports mod)) $+$
  text "" $+$
  vcat (components mod)

print_rascal_module :: [String] -> Module -> IO ()
print_rascal_module options mod' = putStrLn $ render $ gModule mod
  where mod = applyConfig cfg mod' 
        cfg = mkConfig options

program2rascal_module :: Component MixedProgram Module
program2rascal_module = 
  rules_from_flags >>> remove_read_only >>> component_ gProgram

gProgram :: MixedProgram -> Module
gProgram pr@(Program (Spec decls) _) = Module {
    module_name   = ""
  , imports       = []
  , components    = gContext ents ++ map (gRule rel_map) 
                                       (sortBy (flip (on compare priorityOf)) rules)
  }
  where rel_map = M.fromList (zipWith op [1..] (S.toList all_relations))
          where op i rel = (rel, "eval" ++ show i)
        (ents, _, rels, _, rules_or_procs) = partition_decls decls
        rules = lefts rules_or_procs
        all_relations = S.fromList (map (\(RelDecl rel _) -> rel) rels) `S.union` relations rules

gContext :: [EntDecl] -> [Doc]
gContext ents' = [context_decl, empty_context]
  where ents = ents' ++ [EntDecl "res" [ETerm (TVal (Int (-1)))]]
        context_decl = text "data" <+> text "Context" <=> text "ctx" <> gTuple comps <> semi
        comps = map op ents
          where op (EntDecl nm _) = text "value" <+> text nm
        ent_exprs = map op ents
          where op (EntDecl _ e) = gSeq brackets gExpr e
        empty_context = text "Context" <+> text "empty_context" <> parens empty <+> text "{" $+$
                          nest 2 (
                           text "return" <+> text "ctx" <> gTuple ent_exprs <> semi
                          ) $+$ text "}"

gRule :: M.Map String String -> Rule -> Doc
gRule relmap (Rule _ (Concl _ (PConf ps pents) rel (TConf ts tents)) cs _) = 
  text "Context" <+> text fname <> parens args <+> text "{" $+$
    nest 2 (
      bind_entities "ctx" pents $+$
      let after_conditions =  assign_entities "ctx" tents $+$
                              assign_result "ctx" ts $+$
                              text "return" <+> text "ctx" <> semi 
      in foldr (gCond relmap) after_conditions cs
    ) $+$ text "}"
  where fname = case M.lookup rel relmap of
                  Nothing -> error ("relation " ++ rel ++ " not declared")
                  Just nm -> nm
        args = text "Context" <+> text "ctx" <> comma <+> gSeq brackets gPattern ps 
    
bind_entities ctx refs = vcat $ map bind_entity refs
  where bind_entity (eid, p) = gSeq brackets gPattern p <+> text "=" <+> text ctx <.> tentity eid <> semi
assign_entities ctx refs = vcat $ map assign_entity refs
  where assign_entity (eid, t) = text ctx <.> tentity eid <=> gSeq brackets gExpr t <> semi

assign_result ctx ts = text ctx <.> text "res" <=> gSeq brackets gExpr ts <> semi

gCond :: M.Map String String -> Either Premise SideCon -> Doc -> Doc
gCond rm (Left prem) = gPremise rm prem
gCond rm (Right sc)  = gSideCon sc

gPremise :: M.Map String String -> Premise -> Doc -> Doc
gPremise relmap (Prem _ (TConf ts tents) rel (PConf ps pents)) cont = 
  assign_entities "ctx" tents $+$
  text "ctx" <=> text fname <> gTuple [text "ctx", gSeq brackets gExpr ts] <> semi $+$ 
  bind_entities "ctx" pents $+$
  text "if" <> parens (gSeq brackets gPattern ps <+> text ":=" <+> text "ctx" <.> text "res") <+> 
    text "{" $+$ nest 2 cont $+$ text "}" <+> 
    text "else" <+> text "{" <+> text "fail" <> semi <+> text "}" 
  where fname = case M.lookup rel relmap of
                  Nothing -> error ("relation " ++ rel ++ " not declared")
                  Just nm -> nm

gSideCon :: SideCon -> Doc -> Doc
gSideCon sc cont = case sc of 
  SideOP es ps  -> text "if" <> parens (gSeq brackets gPattern ps <+> text ":=" <+>
                                        gSeq brackets gExpr es) <+> text "{" $+$
                                  nest 2 cont $+$ text "}" <+> text "else" <+> 
                                  text "{" <+> text "fail" <> semi <+> text "}"
  Term _ _      -> empty -- TODO
  NonTerm _ _   -> empty -- TODO

gPattern :: Pattern -> Doc
gPattern p = case p of
  PCons f ps  -> text f <> gTuple (map gPattern ps) 
  PVar x      -> tvar x
  PVal v      -> ppLit gPattern v 
  PAny        -> text "_"

gExpr :: Expr -> Doc
gExpr e = case e of 
  ETerm t   -> gTerm t
  VOP op es -> gOP op <> parens (hsep $ intersperse comma $ map gExpr es)

gOP :: VOP -> Doc
gOP op = text op

gTerm :: Term -> Doc
gTerm t = case t of
  TVar x -> tvar x
  TVal v -> ppLit gTerm v
  TCons nm ts -> text nm <> gTuple (map gTerm ts) 

ppLit :: HasValues t => (t -> Doc) -> Values t -> Doc
ppLit gterm v = case v of 
  Int i             -> text (show i)
  v | isString_ v   -> doubleQuotes (text (unString v))
  v | Just c <- upcastCharacter v -> quotes (text (show c))
  ADTVal "true" []    -> text "true"
  ADTVal "false" []   -> text "false"
--  ADTVal nm vs      -> mathit (unpack nm) <> angled (map gterm vs)
--  ComputationType (Type (ADT nm ts))
--0                    -> mathit (unpack nm) <> bracketed (map gterm ts)
  _                 -> text (ppValues (render . gterm) v)


tvar :: String -> Doc
tvar = text 

tentity :: String -> Doc
tentity = text

class HasRels a where
  relations :: a -> S.Set String 

instance HasRels a => HasRels [a] where
  relations = S.unions . map relations

instance HasRels Rule where
  relations (Rule _ (Concl _ _ rel _) _ _) = S.singleton rel 
