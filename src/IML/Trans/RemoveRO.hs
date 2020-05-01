
module IML.Trans.RemoveRO (remove_read_only) where

import IML.Grammar.Mixed
import IML.Grammar.Programs
import IML.Grammar.Specs
import IML.Trans.ProMan

import Funcons.Operations (traverseV)

import Control.Arrow ((***))

remove_read_only :: Component MixedProgram MixedProgram
remove_read_only = component gProgram

gProgram :: MixedProgram -> ProMan MixedProgram
gProgram (Program (Spec ds) qs) = do
      ds' <- mapM (mapM gRuleDecl) ds
      return (Program (Spec ds') qs)

gRuleDecl :: Either Rule ProcDecl -> ProMan (Either Rule ProcDecl)
gRuleDecl (Right r) = return (Right r)
gRuleDecl (Left l)  = Left <$> gRule l

gRule :: Rule -> ProMan Rule
gRule (Rule prio (Concl ros (PConf p ins) r (TConf t outs)) cds vds) = do
  (ins', outs') <- unzip <$> mapM accToUp ros
  cds' <- mapM gCond cds
  return (Rule prio (Concl [] (PConf p (ins'++ins)) r (TConf t (outs'++outs))) cds' vds)

accToUp :: EntAcc -> ProMan (EntAcc, EntUp)
accToUp (eid, pats) = do
  pats' <- mapM gRemWildCards pats
  terms <- mapM gPat2Term pats'
  return ((eid, pats), (eid, (map ETerm terms)))
  where
    gPat2Term :: Pattern -> ProMan Term
    gPat2Term PAny            = error "pat2term: wildcard" 
    gPat2Term p@(PVar x)      = return (TVar x) 
    gPat2Term p@(PCons cs ps) = TCons cs <$> mapM gPat2Term ps
    gPat2Term p@(PVal v)      = TVal <$> traverseV gPat2Term v 

    gRemWildCards :: Pattern -> ProMan Pattern
    gRemWildCards PAny            = PVar <$> fresh_var_
    gRemWildCards p@(PVar _)      = return p
    gRemWildCards p@(PCons cs ps) = PCons cs <$> mapM gRemWildCards ps
    gRemWildCards p@(PVal v)      = PVal <$> traverseV gRemWildCards v

gCond :: Either Premise SideCon -> ProMan (Either Premise SideCon)
gCond (Right sc) = return (Right sc)
gCond (Left (Prem ros (TConf t ins) r (PConf p outs))) = do 
  outs' <- mapM upToAcc ros
  return (Left (Prem [] (TConf t (ros++ins)) r (PConf p (outs'++outs))))

upToAcc :: RoUp -> ProMan EntAcc
upToAcc (eid, expr) = do
  -- pat <- gTerm2Pat term
  -- assuming conclusion's are sound there is no need to pattern match 
  -- in the target of the premise
  --   return (eid, pat)
  return (eid, [PAny])
{-  where
    -- likely to generate duplicate pattern variable!
    -- resolution is to generate fresh-var & equality side-condition
    gTerm2Pat :: Term -> ProMan Pattern
    gTerm2Pat (TVar x)        = return (PVar x)
    gTerm2Pat (TCons cs ps)   = PCons cs <$> mapM gTerm2Pat ps 
    gTerm2Pat (TVal v)        = PVal <$> traverseVM gTerm2Pat v
-}
