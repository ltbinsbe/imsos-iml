
module IML.Trans.ChainReorder where

import IML.Grammar.Grammar
import IML.Trans.ProMan
import IML.Trans.ToGraph

chain :: Component Program Program
chain = reorder 
