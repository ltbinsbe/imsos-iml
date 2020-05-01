{-# LANGUAGE TupleSections, LambdaCase, StandaloneDeriving #-}

module IML.Trans.Bindings where

import IML.Grammar
import IML.Grammar.Bindings
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Trans.ProMan
import IML.Trans.Graphs
import IML.Trans.ToGraph
import IML.Trans.FromGraph

import Control.Monad (when, foldM, forM, forM_)
import Data.List (genericLength)
import qualified Data.Set as S

-- | Unify statements across rules, guaranteeing that `semantically equal'
-- statements are syntactically statements
unify_bindings :: Component (AProgram (AProcDecl [Graph Stmt])) (AProgram (AProcDecl [Stmts]))
unify_bindings = component prog 
  where
    prog :: (AProgram (AProcDecl [Graph Stmt])) -> ProMan (AProgram (AProcDecl [Stmts]))
    prog (Program (Spec decls) qs) = 
          flip Program qs . Spec <$> mapM tdecls decls

    tdecls :: AnyDecls (AProcDecl [Graph Stmt]) -> 
                ProMan (AnyDecls (AProcDecl [Stmts]))
    tdecls (ARuleDecl (Proc i r f gs)) = ARuleDecl . Proc i r f <$> graphs r gs 
    tdecls (AnEntDecl d)              = return $ AnEntDecl d
    tdecls (ARelDecl d)               = return $ ARelDecl d
    tdecls (AVarDecl d)               = return $ AVarDecl d
    tdecls (ATConsDecl d)             = return $ ATConsDecl d

    graphs :: RSymb -> [Graph Stmt] -> ProMan [Stmts] 
    graphs r [] = return []
    graphs r (g:gs) = do
        (_,res) <- foldM group (S.fromList g_nodes, [g_nodes]) gs
        let labels = S.unions (map S.fromList res)
        let local_vsols = map (genericLength . schedules_tl) (g:gs)
        let local_allsols = map (product . enumFromTo 2 . genericLength . nodes) (g:gs)
        let global_dep = dependencies prof_0 (S.toList labels)
        let local_deps = map (dependencies prof_0) res
        add_csv $ [show r,show (length labels)
                  ,show (length global_dep)
                  ,show (length res) 
                  ] ++ map (show . length) res
                    ++ map (show . length) local_deps
                    ++ map show local_vsols
        return res 
      where g_nodes = schedule g 

    group :: (S.Set Stmt, [Stmts]) -> Graph Stmt -> ProMan (S.Set Stmt, [Stmts])
    group (labs,xs) g =  do (labs1,x) <- graph labs [] (schedule g) 
                            return (labs1, xs++[x])

      where graph labs acc [] = return (labs,acc) 
            graph labs acc (s:ss) = s `labelledBy` labs >>= \case 
                Nothing  -> graph (s `S.insert` labs) (acc++[s]) ss
                Just env -> graph labs (acc++[s']) ss'
                  where s'  = sub_mvars env s
                        ss' = sub_mvars env ss
            labelledBy :: Stmt -> S.Set Stmt -> ProMan (Maybe SubsEnv)
            labelledBy s labs = foldM (op s) Nothing (S.toList labs)
              where op snew Nothing slab = unify_with_bias slab snew
                    op _ (Just x) _ = return $ Just x
      
                        
-- | Uniquify bind-variables across rules
uniquify_bindings :: Traversable t => Component (t [Stmts]) (t [Stmts])
uniquify_bindings = component (traverse (traverse group))
  where group :: Stmts -> ProMan Stmts
        group ss = foldM single ss ss
          where single ss' s = do
                  rep_vars <- forM (pvars s) (\v1 -> (v1,) <$> fresh_var_)
                  return (sub_mvars (subsEnvFromList rep_vars) ss')

-- | Check whether in a program all bind-variables are only bound once 
-- per rule and whether all bounded variables are in fact bound.
check_bindings :: Traversable t => Component (t [Stmts]) (t [Stmts])
check_bindings = component (traverse (traverse group))
  where group :: Stmts -> ProMan Stmts
        group ss = do 
          let unbounds = (tvars_set ss S.\\ pvars_set ss) 
                            S.\\ S.singleton prebound_mvar
          when (not (null unbounds)) $
            forM_ unbounds $ \n -> 
              warn ("unbound meta-variable: " ++ show n)
          foldM single S.empty ss -- check for duplicate bind-vars
          -- TODO add check for assumption:
          -- no two statements in the same block are unifiable
          return ss

        single :: S.Set MVar -> Stmt -> ProMan (S.Set MVar)
        single introduced s = foldM mwarn introduced (pvars s)   
          where mwarn :: S.Set MVar -> MVar -> ProMan (S.Set MVar)  
                mwarn old n = do
                  when (n `S.member` old) $
                    warn ("duplicate meta-variable: " ++ show n)
                  return (n `S.insert` old)

