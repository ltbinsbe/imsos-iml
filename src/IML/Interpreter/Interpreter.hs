{-# LANGUAGE LambdaCase #-}

module IML.Interpreter.Interpreter where

import IML.Grammar.Shared hiding (Spec(..))
import IML.Grammar
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Grammar.Mixed
import IML.Interpreter.Types
import IML.Printer (showStmt,showTerm,showQuery)
import IML.Trans.ToLower (gPremise)
import IML.Trans.ProMan (runWithDefaults, Component, component_)
import IML.Trans.RemoveRO (remove_read_only)
import IML.Trans.RelFlags (rules_from_flags)
import IML.Trans.Unmix (unmix)
import IML.CodeGen.Shared

import Control.Arrow((>>>))
import Control.Monad.Writer

import Funcons.Operations (libApp, EvalResult(..),
                           eval, OpExpr(ValExpr,TermExpr))

import Data.Function (on)
import Data.Semigroup ((<>))
import Data.Maybe (isJust, fromJust)
import Data.List (intersperse, sortBy)
import qualified Data.Map as M
import qualified Data.Set as S

-- for debugging
import System.IO.Unsafe
trace a b = b
--trace a b = unsafePerformIO $ (putStrLn a >> return b)

--  Monad for collecting meta-information about the interpreter's execution
type MetaInfo a   = Writer Traces a
type CommitInfo   = (StaticRuleInfo, MetaEnv, Record, Record)
data Traces       = Traces { tr_stmts :: [Stmt]
                           , tr_commits :: [CommitInfo] }

instance Semigroup Traces where
  (<>) = mappend

instance Monoid Traces where
  mempty = Traces mempty mempty
  ts1 `mappend` ts2 = 
    mempty { tr_stmts = (tr_stmts ts1) `mappend` (tr_stmts ts2) 
           , tr_commits = (tr_commits ts1) `mappend` (tr_commits ts2)
           }

newtype QueryRes = QueryRes (Query, Bool, TransS, Traces)

showCommitInfo :: CommitInfo -> String
showCommitInfo (sri, env, ins, outs) = 
  "Rule:    " ++ show (rule_id sri) ++ "\n" ++
  "  Env:   " ++ show env' ++ "\n" ++
  if (null ents) then "" else 
    "  In:    " ++ show ins' ++ "\n" ++
    "  Out:   " ++ show outs' ++ "\n" 
  where ents = ent_ids sri
        env' = showMap $ M.delete prebound_mvar env
        showMap = map keyVal . M.toList
          where keyVal (k,v) = k ++ " |-> " ++ show (map showTerm v)
        ins' = showMap $ M.foldrWithKey selector M.empty ins
        outs'= showMap $ M.foldrWithKey selector M.empty outs
        selector k v m | k `elem` ents = M.insert k v m
                       | otherwise     = m

traceStmt :: Stmt -> MetaInfo ()
traceStmt s = tell (mempty { tr_stmts = [s] })

traceCommit :: CommitInfo -> MetaInfo ()
traceCommit ci = tell (mempty { tr_commits = [ci] })

program2output :: [String] -> Component MixedProgram String 
program2output opts = rules_from_flags >>> remove_read_only >>> unmix >>>
  component_ (unlines . map (showQRes opts) . run)

-- assumes premise contexts have been desugared
showQRes :: [String] -> QueryRes -> String
showQRes opts (QueryRes (q@(Prem _ tconf rel pconf),success,st@(gam,rec),tr))
  | "--trace-stmts" `elem` opts = definite ++
        unlines (map (("  "++) . showStmt) (tr_stmts tr))
  | "--trace-commits" `elem` opts = definite ++ 
        unlines (map (("  "++) . showCommitInfo) (tr_commits tr))
  | otherwise = definite 
  where bindsIn gam = concat $ intersperse "\n" $ 
                [ var ++ " |-> " ++ show (map showTerm t) | (var, t) <- M.assocs gam ]
        optFail | success   = ""
                | otherwise = " FAILED"
        definite = unlines [showQuery q ++ optFail, bindsIn gam, bindsIn rec]

run :: Program -> [QueryRes]
run (Program (Spec ds) qs) = --map (\q -> run1 q envEmpty e0 (tm, gr, rt, css, e0)) qs
                              fst $ foldl propEnvTruQs ([], envEmpty) qs
  where
   propEnvTruQs (qrs,env) q = (qrs++[qr],env `envUnite` fst st)
      where qr@(QueryRes (_, _, st, _)) = run1 q env e0 (tm, gr, rt, css, e0)
   (eds,tcons,relds,vardecls,transds) = partition_decls ds
   (tm,gr) = foldr eTransDecl (transEmpty,globEmpty) transds
   css = foldr eTConsDecl M.empty tcons 
   rt = relFromDecls relds
   e0 = foldr (eEntDecl css) recEmpty eds
    where appFDef _ vl vr = vr

run1 :: Query -> MetaEnv -> Record -> TransC -> QueryRes 
run1 q@(Prem ct tconf r pconf) env rec (tm, gr, rt, css, rec0) =  
  QueryRes (q,not (isBot mt),st,traces)
  where main = runWithDefaults (gPremise 1 q)
        ((mt,st), traces) = runWriter (eStmts main (tm, gr, rt, css, rec) (env, rec)) 

eStmts :: Stmts -> TransC -> TransS -> MetaInfo (StmtValue, TransS)
eStmts [] ctx state = return (Nil, state)
eStmts (s:ss) ctx state = eStmt s ctx state >>= \case 
  (Nil,state')    -> eStmts ss ctx state'
  res             -> return res

{- 
testCondition :: TransS -> Either Premise SideCon -> Bool
testCondition (gam,es) (Left (Trans rel e x ml)) = 
  call rel ct es (tm, gr, rt, css, es) 
-}

eStmt :: Stmt -> TransC -> TransS -> MetaInfo (StmtValue, TransS)
eStmt s ctx@(tm, gr, rt, css, rec0) state@(gam,es) = do
  traceStmt s >> case s of 
    IsTerm r t | checkIfTerminal r t  -> skip
               | otherwise            -> abort 
    IsNonTerm r t | checkIfTerminal r t -> abort
                  | otherwise           -> skip
    PM e ps -> case eExprs (subs_expr gam e) of
      Just ts  -> case matches ts ps of
                    Just gam1 -> returnGam Nil (gam `envUnite` gam1)
                    Nothing -> abort
      Nothing -> abort
    Set eid e i -> entity_set eid e i 
    Get eid x i -> entity_get eid x i 
    Commit t msri -> do
      case msri of Nothing   -> return ()
                   Just sri  -> traceCommit (sri, gam, rec0, es)
      returnNil (Res (ct, es))
       where  ct  = subs gam t 
    Trans rel e x ml -> mkCall rel e x ml
    Branches [] -> abort 
    Branches (ss:sss) -> eStmts ss ctx state >>= \case 
        (Bot, _)  -> eStmt (Branches sss) ctx state 
        res       -> return res 
  where   skip = return (Nil, (gam, es))
          abort = return (Bot, (gam, es)) 
          returnNil a = return (a, (gam, es)) 
          returnGam a gam' = return (a, (gam', es))
          returnEnts a es' = return (a, (gam, es'))

          entity_set :: EID -> [Term] -> Label -> MetaInfo (StmtValue, TransS)
          entity_set eid t l = returnEnts Nil (recInsert eid ct es)
            where ct = subs gam t
          entity_get :: EID -> [MVar] -> Label -> MetaInfo (StmtValue, TransS)
          entity_get eid x l = case entValue es eid of
            Nothing -> error ("no default value for entity:  "++ eid)
            Just t  -> case binds x t of 
                        Nothing   -> abort -- sequences not of matching lengths
                        Just gam1 -> return (Nil, (gam `envUnite` gam1, es))

          mkCall :: RSymb -> [Term] -> [MVar] -> Label -> MetaInfo (StmtValue, TransS)
          mkCall rel t x l = call rel ct es (tm, gr, rt, css, es) 
            >>= \case Just (ct1_,rec2) -> case binds x ct1_ of 
                        Nothing   -> abort -- sequences not of matching lengths
                        Just gam1 -> return (Nil, (gam', rec2)) 
                          where gam'  = gam `envUnite` gam1 
                      _ -> abort 
            where ct      = subs gam t 
  
          checkIfTerminal r t = appender (isVal css r) (subs gam t)
                    where appender | r_eid     = any
                                   | otherwise = all
                           where r_eid = isJust (M.lookup r es)

call :: RSymb -> [Term] {-closed-} -> Record -> TransC -> MetaInfo (Maybe ([Term], Record))
call _ ts _ _ | any isTVar ts = error "call applied to one or more open terms"
call rsymb t ents (_, _, _, css, _) 
  | all (isVal css rsymb) t 
     || any (uncurry (\e ts -> any (isVal css e) ts)) 
          (M.toList ents) = return Nothing
call rel t0 rec0 (tm, gr, rt, css, _) = 
  eStmt (Branches branches) (tm, gr, rt, css, rec0) (prebound_mvar `bind` t0, rec0) >>= \case
    (Res (t, rec1),_) -> return $ Just (t, rec1)
    _                 -> return $ Nothing
  where branches = map snd $ 
                    sortBy (flip compare `on` fst) $ 
                    ((globOf rel gr) ++) $ transOf rel t0 tm 
