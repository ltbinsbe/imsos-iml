
module IML.Trans.ChainReorderFactor where

import IML.Grammar
import IML.Trans.Bindings
import IML.Trans.ToGraph
import IML.Trans.ReorderFactor
import IML.Trans.FromGraph
import IML.Trans.Sanitise
import IML.Trans.ProMan

import Control.Arrow

chain :: Component Program Program 
chain = check_bindings >>> graphify >>> sequentialise >>> remove_rebindings >>> 
            graphify >>> reorder_factor >>> remove_common_rewrites
