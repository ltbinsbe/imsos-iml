
-- | 
-- This module exports a 'Component' adding rules to 'Spec's for 
-- lifting value operations to constructors/
module IML.Trans.ValueOperations where

import IML.EDSL
import IML.Trans.ProMan
import IML.Grammar.Mixed
import IML.Grammar.Programs
import IML.Grammar.Specs
import Funcons.Operations as VOP

import Data.Map (assocs)
import Control.Monad

add_value_operations :: RSymb -> Component MixedProgram MixedProgram 
add_value_operations rsymb = component_ add
  where add (Program (Spec ds) qs) = Program (Spec (ds++map (ARuleDecl. Left) new)) qs
        new = mkRules rsymb

mkRules :: RSymb -> [Rule]
mkRules rsymb = rules
  where Spec new = execRuleBuilder $ mapM_ (uncurry (mkrule rsymb)) 
                                   $ assocs (VOP.library :: Library Term)
        (_,_,_,_,rules) = partition_decls new

        mkrule :: RSymb -> VOP.OP {- String, operation name -} -> VOP.ValueOp t -> RuleBuilder ()
        mkrule rsymb nm op = case op of 
            NullaryExpr _         -> build 0 
            UnaryExpr _           -> build 1
            BinaryExpr _          -> build 2
            TernaryExpr _         -> build 3
            NaryExpr _            -> return ()
         where
          build arity = do 
            build_cong_rules arity nm rsymb -- congruence rules
            -- axiom
            vars <- mapM (const fresh_var) [1..arity]
            lhs (PCons nm (map PVar vars))
            forM_ vars (is_terminating rsymb . TVar) -- termination side conditions
            commit rsymb (vop nm (map TVar vars))   -- contains value operation application

