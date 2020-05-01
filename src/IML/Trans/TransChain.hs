
module IML.Trans.TransChain where

import IML.Grammar.RuleFormat as HIGH 
import IML.Grammar.Grammar as LOW
import IML.Grammar.Shared
import IML.Trans.ToLower
import IML.Trans.ToGraph
import IML.Trans.Graphs
import IML.Trans.FromGraph
import IML.Trans.ReorderFactor
import IML.Trans.ProMan

import Control.Arrow
import qualified Data.Map as M

graph_chain :: Component HIGH.Spec (M.Map (Cons, RSymb) [Graph Stmt]) 
graph_chain = initProgram [] >>> graphify >>> graph_linker
  where graph_linker = component_ (\(Program (LOW.Spec _ spec) _) -> foldr op M.empty spec)
          where op (ARuleDecl (Trans r f gs)) acc = 
                    foldr (\g -> M.insertWith (++) (f,r) [g]) acc gs

chain :: Component HIGH.Spec Program
chain = initProgram []        -- spec -> program
    >>> graphify              -- program -> graphs
    >>> reorder_factor        -- graphs -> program 
