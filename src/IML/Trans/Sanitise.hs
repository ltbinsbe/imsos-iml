
-- | Assuming the statements are in a dependency preserving order,
-- remove certain redundant statements from a sequence of statements.
module IML.Trans.Sanitise where

import IML.Trans.ProMan
import IML.Grammar
import IML.Grammar.Bindings

import qualified Data.Map as M

remove_rebindings :: Functor a => Component (a [Stmts]) (a [Stmts])
remove_rebindings = component_ (fmap (fmap (rMVarRename subsEmpty)))

rMVarRename :: SubsEnv -> Stmts -> Stmts
rMVarRename env ss = case ss of
  []              -> []
  [Branches sss]  -> [Branches (map (rMVarRename env) sss)]
  (s:ss)  -> case sub_mvars env s of
    -- if a pm-statement has just two meta-variables let the first take the
    -- place of the second in all subsequence statements
    PM [ETerm (TVar v1)] [PVar (v2)] 
                  -> rMVarRename (subsInsert v2 v1 env) ss
    Branches sss  -> error "rMVarRename: assert1" 
    s'            -> s' : rMVarRename env ss

type RewEnv = M.Map Term MVar

class HasTerms a where
  sub_terms :: RewEnv -> a -> a 

instance (HasTerms a, HasTerms b) => HasTerms (Either a b) where
  sub_terms env (Left a) = Left (sub_terms env a)
  sub_terms env (Right a) = Right (sub_terms env a)

instance HasTerms Stmt where
  sub_terms env s = case s of
    PM e p          -> PM (map (sub_terms env) e) p
    Branches sss    -> Branches (map (map (sub_terms env)) sss)
    Commit t info   -> Commit (map (sub_terms env) t) info
    Trans r ts vs l -> Trans r (map (sub_terms env) ts) vs l  
    Get _ _ _       -> s
    Set n e l       -> Set n (map (sub_terms env) e) l

instance HasTerms Expr where
  sub_terms env e = case e of
    ETerm t   -> ETerm (sub_terms env t)
    VOP op es -> VOP op (map (sub_terms env) es)

instance HasTerms Term where
  sub_terms env t = case M.lookup t env of
    Nothing -> case t of  TVar v      -> TVar v
                          TVal v      -> TVal v
                          TCons c ts  -> TCons c (map (sub_terms env) ts) 
    Just v  -> TVar v

