{-# LANGUAGE ImplicitParams, PartialTypeSignatures, OverloadedStrings #-}

module IML.CodeGen.DirectHaskell where

import IML.Grammar
import IML.Options
import IML.Grammar.Bindings
import IML.Printer (ppStmt)
import IML.CodeGen.Shared
import IML.CodeGen.HaskellModule
import IML.Trans.ToLower (mergeBy)

import Funcons.Operations (VPattern(..), SeqSortOp(..))
import qualified Funcons.Operations as OP 

import Text.PrettyPrint.HughesPJ
import Control.Monad.State

import Data.Text (pack, unpack)
import Data.List (intercalate)
import Data.Function (on)
import Data.Maybe (catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S

program2hs :: Options -> Program -> HaskellModule
program2hs options (Program (Spec _ els) qsdecls) = 
 HaskellModule Nothing imports ["OverloadedStrings"] entities relations queries $  
    addDefaults entities ++ 
    addSmartCons relTab relations
  where (entdecls, reldecls, procdecls) = partition_decls els
        relTab    = mkRelTable reldecls procdecls 
        entities  = gEntDecls entdecls
          where ?opts = options
        relations = gProcDecls relTab procdecls 
          where ?opts = options
        queries   = zipWith (gQuery relTab) [1..] qsdecls
          where ?opts = options
        imports  = map Right
                    [(["IML","CodeGen","DirectHaskellSupport"], Just "SUP")
                    ,(["Funcons","Operations"], Just "VOP")
                    ,(["Data","Map"], Just "M")
                    ]

        mkRelTable :: [RelDecl] -> [TransDecl] -> RelTable
        mkRelTable rs ts = fst $ foldr op2 (foldr op (M.empty,0) rs) ts
          where op (RelDecl r ps) (relTab,sd) = case M.lookup r relTab of
                  Nothing -> (M.insert r (RelInfo sd ps) relTab, succ sd)
                  Just _  -> (relTab, sd)
                op2 (Trans r _ _) (relTab,sd) = case M.lookup r relTab of
                  Nothing -> (M.insert r (RelInfo sd []) relTab, succ sd)
                  Just _  -> (relTab, sd) 

gQuery :: _ => RelTable -> Int -> Query -> HSDef
gQuery relTab ix (Query term (Rel rel rep _) patt) = 
  (qname, text qname <=> 
    text "SUP.ioAppRes" <+> parens (
      text "SUP.termApp" <+> parens (evalState (gTerm term) emptyGS) <+> 
        text dorep <+> gBool (rel_val_refl relTab rel) <+> dq rel <+>
        text "defaultRO" <+> text "defaultRW"
    ))
  where dorep = case rep of Rep -> "True"
                            NoRep -> "False"
        qname = "query_" ++ show ix

gEntDecls :: _ => [EntDecl] -> Entities
gEntDecls = M.fromListWith (++) . map op
  where op d = (dirOfEDecl d, [(eid, (fname, text fname <+> equals <+> genD d))])
          where eid = eidOfDecl d
                fname = "ent_decl_" ++ lower_hs_name eid
        genD (RODecl eid expr) = evalState (gEntDeclE expr) emptyGS
        genD (RWDecl eid expr) = evalState (gEntDeclE expr) emptyGS
        genD (WODecl eid _ _)  = text "VOP.List []" 

        gEntDeclE :: Expr -> CodeGen Doc 
        gEntDeclE = (((text "SUP.coerceExpr" <+>) . parens) <$>) .  gExpr

addDefaults :: Entities -> [HSDef]
addDefaults ents = 
  [("defaultRO", text "defaultRO" <=> def RO)
  ,("defaultRW", text "defaultRW" <=> def RW)
--  ,("defaultWO", text "defaultWO" <=> def WO)
  ]
  where def dir = text "SUP.entFromList" <+> gList pairs
          where pairs = [ gTuple [dq eid,text f]
                        | (eid,(f,_)) <- maybe [] id (M.lookup dir ents)]

addSmartCons :: RelTable -> Relations -> [HSDef]
addSmartCons relTab rs = 
  map unGroup $ mergeBy ((==) `on` (fst.head)) (++)
      [ [(c,rel)] | (rel,defs) <- M.toList rs, (c,_) <- defs ]
  where unGroup :: [(Cons, RSymb)] -> HSDef
        unGroup xs = (c,mkSmart c (map ((\c -> (c,dq c)). snd) (init xs)
                                   ++ [(snd (last xs), tmp_var 1)]))
          where c = fst (head xs)
        mkSmart c rels = 
          text (call_name c) <+> args_var <=> 
            text "SUP.Term" <+> dq c <+> args_var <+> text "op" $+$ nest 2 
              (text "where" $+$ nest 2 
                 (vcat (map (uncurry mkSingle) 
                    [ (mrep, rel) | rel <- rels, mrep <- [True,False] ])))
          where mkSingle mrep (rel,rvar) = 
                    text "op" <+> rept <+> rvar <=> rep <+> rvar <+> 
                            text (proc_name rrep c) <+> args_var
                  where (rept,rep)  | mrep      = (text "True", text "SUP.tr_many")
                                    | otherwise = (text "False", text "SUP.tr_single")
                        rrep = rel_id $ relTab M.! rel

gProcDecls :: _ => RelTable -> [TransDecl] -> Relations
gProcDecls relTab tds = foldr (op relTab) M.empty tds
  where op relTab (Trans r c sss) acc = 
          M.insertWith (++) r [(c, (tname, entry))] acc
          where tname = proc_name (rel_id (relTab M.! r)) c
                entry = let ?ctx  = StmtContext r c 0 0 relTab
                        in text tname <+> args_var <+> ro_var 0 <+> rw_var_r 0 
                          <+> equals $$ nest 2 (gBody sss)
                

gBody :: _ => [Stmts] -> Doc
gBody sss = 
  let a_body = evalState (case sss of 
                  [ss] -> branchBody ss 
                  _    -> gBranches sss) emptyGS 
  in text "do" <+> (vcat $
      [text "let" <+> wo_var 0 <=> text "SUP.entEmpty"
      ,text "let" <+> rw_var_w 0 <=> text "SUP.entEmpty"] ++
      minitial_env ++
      a_body )
  where minitial_env | haskell_patterns ?opts = []
                     | otherwise = [text "let" <+> env_var <=> text "VOP.envEmpty"]

gBranches :: _ => [Stmts] -> CodeGen [Doc]
gBranches sss = do 
  (bs, docs) <- declBranches sss
  return (docs ++ [text "SUP.evalBranches" <+> gList (map text bs)])

getLastCallLabel :: Stmts -> Int
getLastCallLabel ss = case getCallLabels ss of
  []  -> 0
  xs  -> last xs

getCallLabels :: Stmts -> [Int]
getCallLabels = catMaybes . map op 
  where op s | isCaller s = labelOf s
             | otherwise  = Nothing 

declBranches :: _ => [Stmts] -> CodeGen ([String], [Doc])
declBranches brs = unzip <$> branch_sequence (zipWith mkF [1..] brs)
  where mkF ix br = do
          br_body <- let ?ctx = set_ix ix (inc_depth ?ctx) in branchBody br
          let name = branch_name (stmt_branch_depth ?ctx) ix
          let doc  = text "let" <+> text name <+> equals <+> 
                        text "do" $$ nest 6 (vcat br_body)
                  where lab = getLastCallLabel br
          return (name, doc)
                
branchBody :: _ => Stmts -> CodeGen [Doc]
branchBody ss =
  (initEnvVars (getCallLabels ss) ++) <$> gStmts ss 

initEnvVars :: [Int] -> [Doc]
initEnvVars = concatMap op
  where op i =  [mkLet (ro_var i) (ro_var 0)
                ,mkLet (rw_var_w i) (text "SUP.entEmpty")]

data StmtContext = StmtContext  { stmt_rel          :: RSymb
                                , stmt_cons         :: Cons
                                , stmt_branch_depth :: Int
                                , stmt_branch_ix    :: Int
                                , stmt_rel_table    :: RelTable
                                }

inc_depth :: StmtContext -> StmtContext
inc_depth ctx = ctx { stmt_branch_depth = stmt_branch_depth ctx + 1 }

set_ix :: Int -> StmtContext -> StmtContext
set_ix i ctx = ctx { stmt_branch_ix = i }

gStmts :: _ => [Stmt] -> CodeGen [Doc]
gStmts [] = return []
gStmts (x:xs) = gStmt x xs 

gStmt :: _ => Stmt -> [Stmt] -> CodeGen [Doc]
gStmt s rest = case s of
  PM_Args ps      -> sem_pm_args ps continue failtxt 
  PM expr pat     -> sem_pm expr pat continue failtxt 
  _ -> let current = case s of
            PM_Args _   -> error "gStmt 1"
            PM _ _      -> error "gStmt 1"
            Branches sss -> gBranches sss 
            Commit t     -> sem_commit t 
            Single r t x Nothing  -> bindTy T x >> procCallCF False r t x  
            Single r t x (Just l) -> bindTy T x >> procCallCS False r t x l
            Many r t x Nothing    -> bindTy T x >> procCallCF True r t x
            Many r t x (Just l)   -> bindTy T x >> procCallCS True r t x l
            Unobserv l            -> sem_unobserv l 
            RO_Get eid x   -> sem_ro_get eid x 
            RO_Set eid e l -> sem_ro_set eid e l 
            RW_Set eid e l -> sem_rw_set eid e l 
            RW_Get eid x l -> sem_rw_get eid x l 
            WO_Set eid e   -> sem_wo_set eid e 
            WO_Get eid x l -> sem_wo_get eid x l 
        in (++) <$> current <*> continue 
  where continue = gStmts rest  
        failtxt = doubleQuotes 
                  (text ("`" ++ stmt_rel ?ctx ++ "` rule for `" ++ stmt_cons ?ctx ++ 
                    "`, branch: " ++ bname ++ ", statement: " ++ 
                      (escape $ render $ ppStmt s)))
          where escape [] = []
                escape ('"':xs) = '\\':'"':escape xs
                escape (c:xs) = c:escape xs
                bname = branch_name (stmt_branch_depth ?ctx) (stmt_branch_ix ?ctx) 

sem_pm_args :: _ => [Pattern] -> CodeGen [Doc] -> Doc -> CodeGen [Doc]
sem_pm_args ps succ failtxt  | haskell_patterns ?opts = hs_match 
                             | otherwise              = exp_match 
 where  exp_match = do
          rest <- succ
          return $ [
              env_var <<-> text "SUP.tmatches" <+> args_var <+> 
                gPatterns ps <+> failtxt <+> env_var
            ] ++ rest

        hs_match = do
         forM_ (pvars_set ps) (bindTy T)
         pm_body <- succ
         return [text "let" <+> pm_fun <+> gPatterns ps <+> equals <+> 
                                  text "do" $+$ nest 6 (vcat pm_body)
                ,text "   " <+> pm_fun <+> text "_" <=> pmFail failtxt
                ,text " in" <+> pm_fun <+> args_var]

sem_pm expr pat succ failtxt | haskell_patterns ?opts = hs_match
                             | otherwise              = exp_match
 where  exp_match = do
          (_,edoc) <- gExprOuter expr
          rest <- succ
          return $ [
              tmp_var 1 <<-> edoc
            , env_var <<-> text "SUP.vmatch" <+> tmp_var 1 <+> 
                parens (gVPattern pat) <+> failtxt <+> env_var
            ] ++ rest
    
        hs_match = do 
          forM_ (pvars_set pat) (bindTy V)
          (casts,edoc) <- gExprOuter expr
          pm_body <- succ
          return $ (casts ++) $ 
            case pat of 
              VPMVar x -> [hsVar x <<-> edoc] ++ pm_body
              VPAny   -> [text "_" <<-> edoc] ++ pm_body
              _ -> [tmp_var 1 <<-> edoc
                  ,text "let" <+> pm_fun <+> gVPattern pat <+> equals <+> 
                                      text "do" $+$ nest 6 (vcat pm_body)
                  ,text "   " <+> pm_fun <+> text "_" <=> pmFail failtxt
                  ,text " in" <+> pm_fun <+> tmp_var 1]

sem_commit t = do
  lcl <- gets gs_last_caller 
  let ret_mut | lcl > 0   = text "SUP.unionRW" <+> rw_var_w 0 <+> rw_var_w lcl
              | otherwise = rw_var_w 0
      ret_out | lcl > 0   = text "SUP.unionWO" <+> wo_var 0 <+> wo_var lcl
              | otherwise = wo_var 0
  tdoc <- gTermOuter t
  return [text "return" <+> gTuple [parens tdoc, ret_mut, ret_out]]

sem_wo_get eid x l = do
  bindTy V x
  return $ [hsVar x <<-> mkMaybe (parens $ text "List []") (text "id")
                         (text "SUP.entLookup" <+> dq eid <+> wo_var l)
           ,mkLet (wo_var l) (text "SUP.entDelete" <+> dq eid <+> wo_var l)] ++
              sem_bind True x

sem_wo_set eid e = do 
  (casts, edoc) <- gExprOuter e 
  return $ casts ++
     [tmp_var 1 <<-> edoc
     ,wo_var 0 <<-> mkReturn (mkInsert "SUP.entInsert" (dq eid) (tmp_var 1)
         (wo_var 0))]

sem_rw_get eid x l = do
  bindTy V x
  return $ 
     [text "SUP.assert" <+> parens (text "SUP.entMember" <+> dq eid <+> 
        rw_var_r 0) <+> gString ("no default value for entity: " ++ eid)
     ,mkLet (hsVar x) (mkMaybe (parens $ mkLookup (dq eid) (rw_var_r 0)) 
            (text "id") (text "SUP.entLookup" <+> dq eid <+> rw_var_w l))
     ,rw_var_w l <<-> text "return" <+> parens (text "SUP.entDelete" <+> 
          dq eid <+> rw_var_w l)] ++ sem_bind True x

sem_rw_set eid e l = do 
  (casts,edoc) <- gExprOuter e
  return $ casts ++ 
          [tmp_var 1 <<-> edoc
          ,rw_var_w l <<-> mkReturn 
            (mkInsert "SUP.entInsert" (dq eid) (tmp_var 1) (rw_var_w l))]

sem_ro_set eid e l = do 
  (casts,edoc) <- gExprOuter e
  return $ casts ++
          [tmp_var 1 <<-> edoc 
          ,ro_var l <<-> mkReturn (mkInsert "SUP.entInsert" (dq eid) (tmp_var 1) (ro_var l))]

sem_ro_get eid x = do
  bindTy V x
  return $ [text "SUP.assert" <+> parens (text "SUP.entMember" <+> dq eid <+> 
            ro_var 0) <+> gString ("no default value for entity: " ++ eid)
              ,mkLet (hsVar x) (mkLookup (dq eid) (ro_var 0))] ++ sem_bind True x

sem_unobserv l = return
  [assert_op $ parens (text "SUP.entNull" <+> rw_var_w l)
  ,assert_op $ parens (text "SUP.entNull" <+> wo_var l) ]
  where assert_op v = text "SUP.assert" <+> v <+> gString ("unobserv " ++ show l)

procCallCF :: _ => Bool -> RSymb -> Term -> MVar -> CodeGen [Doc]
procCallCF many r t x = do 
  tdoc <- gTermOuter t
  return $ procCall r x tdoc many 
              (text "_") (text "_") (text "emptyEnv") (text "emptyEnv")

procCallCS :: _ => Bool -> RSymb -> Term -> MVar -> Label -> CodeGen [Doc]
procCallCS many r t x l = do
          lcl <- gets gs_last_caller
          repCaller l
          tdoc <- gTermOuter t
          return $  
            (if lcl == 0 then [] else 
              [rw_var_r 0 <<-> mkReturn (text "SUP.unionRW" <+> rw_var_r 0 <+> rw_var_w lcl)
              ,wo_var 0 <<-> mkReturn (text "SUP.unionWO" <+> wo_var 0 <+> wo_var lcl)]) ++
            procCall r x tdoc many (rw_var_w l) (wo_var l) (ro_var l)
              (parens (text "SUP.unionRW" <+> rw_var_r 0 <+> rw_var_w l))

procCall r x tdoc many rww wo ro rwr = 
          [gTuple [hsVar x, rww, wo] <<-> text "SUP.termApp" <+> parens tdoc
                    <+> gBool many <+> gBool (rel_val_refl (stmt_rel_table ?ctx) r)
                    <+> dq r <+> ro <+> rwr] ++ sem_bind False x

sem_bind :: _ => Bool -> MVar -> [Doc]
sem_bind valMatch x 
  | haskell_patterns ?opts = []
  | otherwise = [env_var <<-> text "SUP.match" <+> hsVar x <+> 
                    parens (text $ show $ mvar2VPattern x) <+> dq "" <+> env_var]
 
-- | Generate a Doc representing an operator-expressions (2nd result
-- and already having evalExpr applied to it)
-- as well as Doc representing casting actions for the meta-variables
-- in the expression.
gExprOuter :: _ => Expr -> CodeGen ([Doc],Doc)
gExprOuter expr = do
  casted  <- M.keysSet <$> gets gs_casted
  casts   <- mapM castVar (S.toList (tvars_set expr `S.difference` casted))
  edoc    <- gExpr expr
  return $ (concat casts, text "SUP.evalExpr" <+> parens edoc)
  where castVar :: _ => MVar -> CodeGen [Doc]
        castVar x | not (haskell_patterns ?opts) = return []
                  | otherwise =  do 
                       ty <- typeOf x
                       case ty of  
                        T -> do x' <- genMVar
                                repCast x x'
                                return $ [hsVar x' <<-> text "SUP.term2Expr" <+> hsVar x]
                        V -> return $ [] 

-- | Generate a Doc representing an operator-expression from an Expr
gExpr :: _ => Expr -> CodeGen Doc
gExpr e = case e of
  Val t -> case t of TVar x | haskell_patterns ?opts -> 
                      typeOf x >>= \ty -> case ty of
                                  T -> getCast x >>= return . hsVar
                                  V -> def 
                     _       -> def
   where def = return (text "VOP.ValExpr" <+> parens (gValuesOuter t))
  VOP op es -> (text (op2fname op) <+>) . gList <$> mapM gExpr es
  where op2fname nm = ("VOP." ++) $ lower_hs_name nm ++ "_"


gValues :: _ => Term -> Doc
gValues (TVar x)  | haskell_patterns ?opts  = hsVar x
                  | otherwise               = text "VOP.VHolder" <+> dq (show x)
gValues (TVal v) = text $ OP.ppValues v
gValues (TCons c cs) = empty 

gValuesOuter :: _ => Term -> Doc
gValuesOuter v = msubstitute $ gValues v
  where msubstitute | haskell_patterns ?opts  = id 
                    | otherwise               = 
                        (text "SUP.substituteVal" <+> env_var <+>) . parens

-- | Generate a Doc representing a value pattern
gVPattern :: _ => Pattern -> Doc
gVPattern p | haskell_patterns ?opts = case p of
  VPAny       -> text "_"
  VPMVar x    -> hsVar x
  VPLit v     -> text (OP.ppValues v)
  VPADT c cs  -> parens (text "VOP.ADTVal" <+> text (unpack c) <+> gList (map gVPattern cs))
            | otherwise = text $ show $ p
 
gTerm :: _ => Term -> CodeGen Doc
gTerm t = case t of
  TVar x -> sem_term_var x
  TVal v -> return $ text "SUP.Val" <+> parens (text (OP.ppValues v))
  TCons c cs -> ((text (call_name c) <+>) . gList) <$> mapM gTerm cs

sem_term_var :: _ => MVar -> CodeGen Doc
sem_term_var x | haskell_patterns ?opts = do
                    ty <- typeOf x
                    case ty of 
                      T -> return (hsVar x)
                      V -> return $ text "SUP.Val" <+> hsVar x
               | otherwise = return (text "SUP.Var " <+> dq (show x))

gTermOuter :: _ => Term -> CodeGen Doc
gTermOuter t = msubstitute <$> gTerm t
  where msubstitute | haskell_patterns ?opts  = id
                    | otherwise               = 
                        (text "SUP.substitute" <+> env_var <+>) . parens


-- | Generate a Doc representing a VPattern from an MVar
mvar2VPattern :: MVar -> VPattern Term 
mvar2VPattern = mvar2pattern VPMVar VPSeqVar

mvar2pattern :: (String -> a) -> (String -> SeqSortOp -> a) -> MVar -> a
mvar2pattern nrm seq = nrm

-- | Generate a Doc representing a list of patterns
gPatterns :: _ => [Pattern] -> Doc
gPatterns = gList . map gVPattern


{-
withValueCons :: (a -> Doc) -> (Cons -> a -> Doc) -> Cons -> [a] -> Doc
withValueCons rec extract c cs = case c of
  "list"  -> text "VOP.List" <+> gList (map rec cs)
  "tuple" -> case cs of 
                []    -> text "VOP.EmptyTuple"
                [c1]  -> rec c1
                (c1:(c2:cs)) -> text "VOP.NonEmptyTuple" <+> parens (rec c1) <+>  
                                  parens (rec c2) <+> gList (map rec cs)
  "integer" -> case cs of 
                [t] -> text "VOP.Int" <+> extract c t 
                _ -> empty 
  "true" -> text "VOP.ADTVal \"true\" []"
  "false" -> text "VOP.ADTVal \"false\" []"
  "identifier" -> case cs of
                    [t] -> extract c t
                    _ -> empty 
  _       -> empty
-}

call_name c = lower_hs_name c ++ "_"
proc_name rrep c =  "sem_" ++ show rrep ++ "_" ++ lower_hs_name c    
env_var = text "env"
args_var = text "fargs"
tmp_var i = text ("tmp0" ++ show i)
ro_var i = text ("ro" ++ show i)
rw_var_w i = text ("rww" ++ show i)
rw_var_r i = text ("rwr" ++ show i)
wo_var i = text ("wo" ++ show i)
pm_fun   = text "pm"
branch_name dep ix = "branch_" ++ show dep ++ "_" ++ show ix

-- ==== CODE GEN MONAD ==== --
type CodeGen a = State GenState a 
data GenState  = GenState { gs_tyenv        :: TyEnv
                          , gs_last_caller  :: Label
                          , gs_casted       :: M.Map MVar MVar
                          , gs_mvar_seed    :: Int
                          }
emptyGS :: GenState
emptyGS = GenState M.empty 0 M.empty 0

type TyEnv  = M.Map MVar Ty
data Ty     = V | T

typeOf :: MVar -> CodeGen Ty
typeOf x = do 
  tyenv <- gets gs_tyenv
  case M.lookup x tyenv of
    Nothing -> error ("unknown meta-var: " ++ show x)
    Just ty -> return ty

bindTy :: Ty -> MVar -> CodeGen ()
bindTy ty x = modify modifier
  where modifier st = st {gs_tyenv = M.insertWith op x ty (gs_tyenv st)}
        op _ _ = error ("duplicate binding var: " ++ show x)

repCaller :: Label -> CodeGen ()
repCaller l = modify modifier
  where modifier st = st { gs_last_caller = l }
 
repCast :: MVar -> MVar -> CodeGen ()
repCast x y = modify modifier
  where modifier st = st { gs_casted = M.insert x y (gs_casted st) }

getCast :: MVar -> CodeGen MVar
getCast x = do  casts <- gets gs_casted
                case M.lookup x casts of
                  Nothing -> error ("uncasted variable: " ++ show x)
                  Just x' -> return x'

genMVar :: CodeGen MVar
genMVar = do  seed <- gets gs_mvar_seed 
              modify (modifier (succ seed))
              -- TODO this relies on having different prefix from
              -- ProMan mvar-generation. Maybe fix to use ProMan
              -- (which should not be reset by branch_sequence!)
              return ("__x" ++ show seed)
  where modifier sd' st = st { gs_mvar_seed = sd' }

-- | Version of sequence that resets state before and after each computations 
branch_sequence :: [State s a] -> State s [a]
branch_sequence cs =  do  st <- get
                          xs <- branch_sequence' cs 
                          put st
                          return xs
  where branch_sequence' [] = return []
        branch_sequence' (c:cs) = do  st <- get
                                      x <- c
                                      put st
                                      xs <- branch_sequence' cs
                                      return (x:xs) 

pmFail txt = text "SUP.pmFail" <+> txt 

instance Show t => Show (VPattern t) where
  show (VPMVar mvar)      = "VOP.VPMVar " ++ show mvar
  show (VPSeqVar mvar op) = "VOP.VPSeqVar " ++ show mvar ++ withinParens op
  show (VPAny)            = "VOP.VPAny "
  show (VPLit v)          = "VOP.VPLit (" ++ showVOPvalue v ++ ")"
  show (VPTuple ps)       = "VOP.VPTuple " ++ showArgs ps
  show (VPList ps)        = "VOP.VPList " ++ showArgs ps
  show (VPADT cs ps)      = "VOP.VPADT " ++ unpack cs ++ showArgs ps

showArgs :: (Show a) => [a] -> String
showArgs as = "[" ++ intercalate "," (map show as) ++ "]"
withinParens :: (Show a) => a -> String
withinParens a = "(" ++  show a  ++ ")"

showVOPvalue :: Show t => OP.Values t -> String 
showVOPvalue (OP.ADTVal nm vs) = "VOP.ADTVal " ++ show nm ++ showArgs vs
showVOPvalue v = show v

