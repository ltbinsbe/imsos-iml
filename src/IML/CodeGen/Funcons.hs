
module IML.CodeGen.Funcons where

import IML.Grammar
import IML.CodeGen.Shared
import IML.CodeGen.HaskellModule

import Text.PrettyPrint.HughesPJ

import Data.Either
import qualified Data.Map as M

spec2hs :: Spec -> HaskellModule
spec2hs els = HaskellModule ["Main"] [["Funcons","Exports"]] ["OverloadedStrings"]
  (gEntDecls (lefts els)) (gProcDecls (rights els))

gEntDecls :: [EntDecl] -> Entities
gEntDecls = map op
  where op d = (eid, (fname, text fname <+> equals <+> genD d))
          where eid = eidOfDecl d
                fname = "ent_decl_" ++ lower_hs_name eid
        genD (RODecl eid expr) = text "DefInherited" <+> dq eid <+> parens (gExprFuncons expr)
        genD (RWDecl eid expr) = text "DefMutable" <+> dq eid <+> parens (gExprFuncons expr)
        genD (WODecl eid _ _)  = text "DefOutput" <+> dq eid

gProcDecls :: [TransDecl] -> Relations
gProcDecls = (\(x,y,z) -> x) . foldr op (M.empty,M.empty,0)
  where op (Trans r c sss) (acc,relID,sd) = 
          (M.insertWith (++) r [(c, (tname, entry))] acc, relID', sd')
          where tname = "proc_decl_" ++ rrep ++ "_" ++ c
                entry = text tname <+> args_var <+> ro_var 0 <+> rw_var_r 0 
                          <+> equals $$ nest 2 (gBody sss)
                (rrep, relID', sd') = case M.lookup r relID of
                  Just i  -> (show i, relID, sd)
                  Nothing -> (show sd, M.insert r sd relID, sd+1)

gBody :: [Stmts] -> Doc
gBody sss = text "do" <+> (vcat $
    [text "let" <+> env_var <=> text "emptyEnv"
    ,text "let" <+> wo_var 0 <=> text "emptyOUT"
    ,text "let" <+> rw_var_w 0 <=> text "emptyMUT"] ++
    (case sss of 
      [ss]  -> concatMap (gStmt (getFirstCallLabel (reverse ss)) 1) ss
      _     -> gBranches 0 sss)
  )

gBranches :: Int -> [Stmts] -> [Doc]
gBranches depth sss = docs ++ [text "evalBranches" <+> gList (map text bs)]
  where (bs, docs) = declBranches 0 sss

getFirstCallLabel :: Stmts -> Int
getFirstCallLabel ss = case dropWhile (not . isCaller) ss of
  []                          -> 0
  x:xs  | Just l <- labelOf x -> l
        | otherwise           -> getFirstCallLabel xs

declBranches :: Int -> [Stmts] -> ([String], [Doc])
declBranches depth brs = unzip (zipWith mkF [1..] brs)
  where mkF ix br = (name, doc)
          where name = "branch_" ++ show depth ++ "_" ++ show ix
                doc = text "let" <+> text name <+> equals <+> 
                        text "do" $$ nest 6 (vcat (concatMap (gStmt lab (depth+1)) br))
                  where lab = getFirstCallLabel (reverse br)

gStmt :: Label -> Int -> Stmt -> [Doc]
gStmt last_caller depth s = case s of
  Branches sss    -> gBranches depth sss
  PM_Args ps      -> [env_var <<-> text "fsMatch" <+> args_var <+> 
                         gList (map gFPattern ps) <+> env_var]
  PM expr pat     -> [tmp_var <<-> text "subsAndRewrite" <+> parens (gExprFTerm expr) <+> env_var
                     ,env_var <<-> text "fMatch" <+> tmp_var <+> parens (gFPattern pat)]
  Commit t        -> [tmp_var <<-> text "substitute" <+> parens (gFTerm t)
                     ,text "return" <+> gTuple [tmp_var, ret_mut, ret_out]]
    where ret_mut | last_caller > 0 = text "unionMUT" <+> rw_var_w 0 <+> rw_var_w last_caller
                  | otherwise = rw_var_w 0
          ret_out | last_caller > 0 = text "unionOUT" <+> wo_var 0 <+> wo_var last_caller
                  | otherwise = wo_var 0
  _               -> [empty]

-- | Generate a Doc representing Funcons from an Expr
gExprFuncons :: Expr -> Doc
gExprFuncons (Val t) = gFuncons t
gExprFuncons (VOP op []) = text "FName" <+> (dq op)
gExprFuncons (VOP op xs) = text "FApp" <+> (dq op) <+> (gList (map gExprFuncons xs))

-- | Generate a Doc representing an FTerm from an Expr
gExprFTerm :: Expr -> Doc
gExprFTerm e = case e of
  Val t -> gFTerm t
  VOP op [] -> text "TName" <+> dq op
  VOP op es -> text "TApp" <+> dq op <+> gList (map gExprFTerm es)

-- | Generate a Doc representing an operator-expression from an Expr
gExpr :: Expr -> Doc
gExpr e = case e of
  Val t -> gValues t
  VOP op es -> text (op2fname op) <+> gList (map gExpr es)
  where op2fname = lower_hs_name 

-- | Generate a Doc representing an FTerm
gFTerm :: Term -> Doc
gFTerm t = case t of
  TVar x                -> text "TVar" <+> dq x
--  TCons True _ _        -> text "TFuncon" <+> parens (gFuncons t)
  TCons _ "list" ts     -> text "TList" <+> gList (map gFTerm ts)
  TCons _ "tuple" ts    -> text "TTuple" <+> gList (map gFTerm ts)
  TCons _ "set" ts      -> text "TSet" <+> gList (map gFTerm ts)
  TCons _ "map" ts      -> text "TMap" <+> gList (map gFTerm ts)
  TCons _ c []          -> text "TName" <+> dq c
  TCons _ c ts          -> text "TApp" <+> dq c <+> gList (map gFTerm ts)

-- | Generate a Doc representing Funcons from a Term
gFuncons :: Term -> Doc
gFuncons t = case t of
  TVar _            -> error "gFuncons"
  TCons True _ _    -> text "FValue" <+> parens (gValues t)
  TCons False c []  -> text "FName" <+> dq c
  TCons False c cs  -> text "FApp" <+> dq c <+> gList (map gFuncons cs)

gValues :: Term -> Doc
gValues (TVar _) = error "gValues"
gValues (TCons False _ _ ) = error "gValues - non-value"
gValues (TCons True "thunk" [t@(TCons False "thunk" _)]) = text "Thunk" <+> parens (gFuncons t)
gValues (TCons True c cs) = case c of
  "list"  -> text "List" <+> gList (map gFuncons cs)
  "tuple" -> case cs of 
                []    -> text "EmptyTuple"
                [c1]  -> gValues c1
                (c1:(c2:cs)) -> text "NonEmptyTuple" <+> parens (gValues c1) <+>  
                                  parens (gValues c2) <+> gList (map gValues cs)
  _       -> empty

-- | Generate a Doc representing an FPattern
gFPattern :: Pattern -> Doc
gFPattern p = case p of
  PAny        -> text "PWildCard"
  PVar x      -> text "PMetaVar" <+> dq x
  PCons _  _  -> text "PValue" <+> parens (gVPattern p)

-- | Generate a Doc representing an VPattern
gVPattern :: Pattern -> Doc
gVPattern p = case p of 
  PAny        -> text "VPWildCard"
  PVar x      -> text "VPMetaVar" <+> dq x
  PCons c ps  -> case c of
          "list"    -> text "PList" <+> gList (map gVPattern ps)
          "tuple"   -> text "PTuple" <+> gList (map gVPattern ps)
          _         -> text "PADT" <+> dq c <+> gList (map gVPattern ps)

lower_hs_name :: String -> String
lower_hs_name = map unhypen
  where unhypen '-' = '_' 
        unhypen c   = c

env_var = text "env"
args_var = text "fargs"
tmp_var = text "tmp0"
ro_var i = text ("ro" ++ show i)
rw_var_w i = text ("rww" ++ show i)
rw_var_r i = text ("rwr" ++ show i)
wo_var i = text ("wo" ++ show i)
