
module IML.Parser.Shared where

import IML.Grammar.High
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Grammar.Mixed

-- A program fragment is
data Fragment = FEntity EntDecl             -- an entity declaration
              | FRelation RelDecl           -- a rule declaration
              | FTermCons TConsDecl         -- a terminal constructor declaration
              | FQuery Query                -- a query
              | FResetEnv                   -- directive for clearing all bindings
              | FProc ProcDecl              -- procedure declaration
              | FRule Rule                  -- an inference rule

mkProgram :: [Fragment] -> MixedProgram  
mkProgram es = Program (Spec rest) interactions
         where (rest,interactions) = foldr op ([],[]) es
                  where op r (rest,qs) = case r of
                            FTermCons td  -> (ATConsDecl td:rest,qs)
                            FProc decl    -> (ARuleDecl (Right decl):rest,qs)
                            FRule rule    -> (ARuleDecl (Left rule):rest,qs)
                            FEntity ent   -> (AnEntDecl ent:rest,qs)
                            FRelation rel -> (ARelDecl rel:rest,qs)
                            FQuery q      -> (rest,DoQuery q:qs)
                            FResetEnv     -> (rest,ResetEnv:qs)

