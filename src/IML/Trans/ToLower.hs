{-# LANGUAGE OverloadedStrings #-}

module IML.Trans.ToLower where

import IML.Grammar.Specs 
import IML.Grammar.Shared 
import IML.Grammar.High as HIGH
import IML.Grammar.Low as LOW
import IML.Trans.ProMan

import Funcons.Operations (Values(ADTVal,ComputationType), ComputationTypes(Type), Types(ADT))

import Control.Monad (liftM2,foldM)

import Data.Maybe (isNothing)
import Data.Text (pack, unpack)

infixr 5 <++>
(<++>) :: ProMan Stmts -> ProMan Stmts -> ProMan Stmts
(<++>) = liftM2 (++)

infixr 5 <++
(<++) :: ProMan Stmts -> Stmts -> ProMan Stmts 
p <++ as = p <++> return as

infixr 5 ++>
(++>) :: Stmts -> ProMan Stmts -> ProMan Stmts
as ++> q = return as <++> q

tRule_ :: Rule -> ProMan ProcDecl 
tRule_ rule = toBranches <$> tRule rule
  where toBranches (Proc prio r f [Branches sss]) = Proc prio r f sss
        toBranches (Proc prio r f ss)             = Proc prio r f [ss]

tRule :: Rule -> ProMan (AProcDecl Stmts)
tRule rule@(Rule prio cl@(Concl _ (PConf ps _) rel _) _ vds) = 
  Proc prio rel (mkStaticPattern (mkVarMap vds) ps) <$> gRuleBody rule

gRuleBody :: Rule -> ProMan Stmts
gRuleBody (Rule _ (Concl _ (PConf lhs ins) rel (TConf rhs outs)) conds _) = 
    pats ++>
    gets 0 ins <++>
    gConditions conds <++>
    sets 0 outs <++>
    commit 
  where pats = [PM [ETerm $ TVar prebound_mvar] lhs]
        commit = do 
          rid <- fresh_id 
          let sinfo = Just $ SRI rid (map fst ins)
          if all isTerm rhs 
            then return [Commit (map unTerm rhs) sinfo]
            else do xs <- mapM (const fresh_var_) rhs
                    return [PM rhs (map PVar xs), Commit (map TVar xs) sinfo]

gConditions :: [Either Premise SideCon] -> ProMan Stmts
gConditions eps = snd <$> foldM mAss (1,[]) eps
  where mAss (seed,acc) (Left p)   = do p' <- gPremise seed p
                                        return (succ seed, acc ++ p')
        mAss (seed,acc) (Right sc) = do sc' <- gSideCond sc 
                                        return (seed, acc ++ sc')

-- assumes turnstile entity references have been desugared
gPremise :: Label -> Premise -> ProMan Stmts
gPremise l (Prem _ (TConf lhs ins) rel (PConf rhs outs)) = 
  sets l ins <++> 
  gTrans l lhs rel rhs <++>
  gets l outs

gTrans :: Label -> [Expr] -> RSymb -> [Pattern] -> ProMan Stmts
gTrans l exprs rel ps
  | allTerms, allVars = return [Trans rel exprs' ps' l]
  | allTerms = do   
      xs <- mapM (const fresh_var_) ps -- TODO update when sequence-patterns exist
      return ([Trans rel exprs' xs l, PM (map (ETerm . TVar) xs) ps])
  | otherwise = do 
      xs <- mapM (const fresh_var_) exprs -- TODO update when sequence-patterns exist (substitution may cause the length of `exprs` to change
      ((PM exprs (map PVar xs)):) <$> gTrans l (map (ETerm . TVar) xs) rel ps
  where allTerms = all isTerm exprs
        exprs'   = map unTerm exprs
        allVars  = all isPVar ps
        ps'      = map unPVar ps

gSideCond :: SideCon -> ProMan Stmts
gSideCond (Term r es)
  | all isTerm es = return [IsTerm r (map unTerm es)]
  | otherwise = do 
      vars <- mapM (\_ -> fresh_var_) es
      (PM es (map PVar vars):) <$> gSideCond (Term r (map (ETerm . TVar) vars))
gSideCond (NonTerm r es) 
  | all isTerm es = return [IsNonTerm r (map unTerm es)]
  | otherwise     = do 
      vars <- mapM (\_ -> fresh_var_) es
      (PM es (map PVar vars):) <$> gSideCond (NonTerm r (map (ETerm . TVar) vars))
gSideCond (SideOP es ps) 
  | all isPVar ps = return [PM es ps]
  -- split in two:
  -- * increases the efficiency of left-factoring
  -- * makes left-factoring more costly
  | otherwise = do 
      b <- boolOpt opt_split_pm
      if b then do  xs <- mapM (const fresh_var_) ps
                    return [PM es (map PVar xs), PM (map (ETerm . TVar) xs) ps]
           else return [PM es ps]

-- setters
sets :: Label -> [EntUp] -> ProMan Stmts
sets l = (concat <$>) . mapM (set l)

set :: Label -> EntUp -> ProMan Stmts
set l (eid, es) | all isTerm es = return [Set eid ts l]
                    where ts = map unTerm es
set l (eid, es) = do xs <- mapM (const fresh_var_) es
                     ((PM es (map PVar xs)):) <$> set l (eid, (map (ETerm. TVar) xs))

-- rw get
gets :: Label -> [EntAcc] -> ProMan Stmts
gets l = (concat <$>) . mapM (get l)

get :: Label -> EntAcc -> ProMan Stmts
get l (eid, ps) | all isPVar ps = return [Get eid xs l]
                    where xs = map unPVar ps
get l (eid, ps) = do xs <- mapM (const fresh_var_) ps
                     return [Get eid xs l, PM (map (ETerm . TVar) xs) ps]


