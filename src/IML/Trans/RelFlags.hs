
module IML.Trans.RelFlags where

import IML.Grammar.Shared
import IML.Grammar.Mixed
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Trans.ProMan
import IML.Trans.ValueOperations (mkRules)

import Data.List (elem)

rules_from_flags :: Component MixedProgram MixedProgram 
rules_from_flags = component update_spec

update_spec :: MixedProgram -> ProMan MixedProgram
update_spec (Program (Spec ds) qs) = do
  let (_, _, reldecls,_,_) = partition_decls ds
  -- general reflexivity rules
  refl_rules <- mapM gReflRule (selectRelSymbs (elem Reflexive )reldecls)
  -- rules for repeated transitions
  rep_rules <- concat <$> mapM gRepetition (selectRelSymbs (elem Repeatable) reldecls)
  -- lifted value operations
  vop_rules <- concat <$> mapM gValOps (selectRelSymbs (elem HasValueOps) reldecls)
  -- merge all new rules
  let new_rules = map (ARuleDecl . Left) $ refl_rules ++ rep_rules 
  -- return a new specification
  return $ Program (Spec ((map rmRelFlags ds) ++ new_rules)) qs
 where selectRelSymbs :: ([RelPred] -> Bool) -> [RelDecl] -> [RSymb]
       selectRelSymbs flag_pred = foldr op [] 
         where op (RelDecl r flags) acc | flag_pred flags = r : acc
                                        | otherwise = acc
       rmRelFlags :: (AnyDecls a) -> AnyDecls a
       rmRelFlags (ARelDecl (RelDecl r flags)) = ARelDecl (RelDecl r flags')
          where flags' = filter (not . handled) flags
                handled Reflexive = True
                handled Repeatable = True
                handled HasValueOps = True
                handled Orderable = False
                handled IsPure = False
       rmRelFlags (AnEntDecl e) = AnEntDecl e
       rmRelFlags (ATConsDecl t) = ATConsDecl t
       rmRelFlags (ARuleDecl r) = ARuleDecl r
       rmRelFlags (AVarDecl v) = AVarDecl v

gTermReflRule :: RSymb -> ProMan Rule
gTermReflRule rsymb = do 
  x <- fresh_var_ 
  let concl = Concl [] (PConf [PVar x] []) rsymb (TConf [ETerm (TVar x)] [])
  -- side condition that checks whether the program component is terminal
  -- whether any entity is terminal is not checked by IML
  let sc    = Right (Term rsymb [ETerm $ TVar x])
  return (Rule 1 concl [sc] [])
 
gReflRule :: RSymb -> ProMan Rule
gReflRule rel = do 
  x <- fresh_var_ 
  let concl = Concl [] (PConf [PVar x] []) rel (TConf [ETerm (TVar x)] [])
  return (Rule 0 concl [] [])
  
-- Repetition will be expressed,
-- despite the lack of any mechanism for ensuring the termination of 
--    arbitrary entities. 
--  * legality / unobservability of transitions
--  * non-terminating left-hand sides
-- These constraints need to be imposed otherwise, by the system.
-- generating IML rules/procedures
gRepetition :: RSymb -> ProMan [Rule]
gRepetition rsymb = do
  let r_star = mRel rsymb
  refl_rule <- gTermReflRule r_star -- write out termination rule instead
  x1 <- fresh_var_
  x2 <- fresh_var_
  v1 <- fresh_var_
  let concl = Concl [] (PConf [PVar x1] []) r_star (TConf [ETerm (TVar v1)] [])
  let prem1 = Prem [] (TConf [ETerm (TVar x1)] []) rsymb (PConf [PVar x2] []) 
  let prem2 = Prem [] (TConf [ETerm (TVar x2)] []) r_star (PConf [PVar v1] [])
  let rule  = Rule 2 concl [Left prem1, Left prem2] []
  return [refl_rule, rule]
  where gTermReflRule r_star = do
          x <- fresh_var_ 
          let concl = Concl [] (PConf [PVar x] []) r_star (TConf [ETerm (TVar x)] [])
          -- side condition that checks whether the program component is terminal
          -- whether any entity is terminal is not checked by IML
          let sc    = Right (Term rsymb [ETerm $ TVar x])
          return (Rule 1 concl [sc] [])


gValOps :: RSymb -> ProMan [Rule]
gValOps rsymb = return (mkRules rsymb) 
