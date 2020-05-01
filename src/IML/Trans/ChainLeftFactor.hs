
module IML.Trans.ChainLeftFactor where

import IML.Grammar
import IML.Trans.Bindings
import IML.Trans.ToGraph
import IML.Trans.LeftFactor
import IML.Trans.FromGraph
import IML.Trans.Sanitise
import IML.Trans.ProMan

import Control.Arrow

chain :: Component Program Program 
chain = check_bindings >>> graphify >>> sequentialise >>> remove_rebindings >>> 
          left_factor >>> remove_common_rewrites

