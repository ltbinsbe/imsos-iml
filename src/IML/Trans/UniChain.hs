-- | Component chain applying a unification pre-processing step
-- Given a program, produces a program in which `unifiable' statements
-- are now syntactically equal
module IML.Trans.UniChain where

import IML.Grammar
import IML.Trans.Bindings
import IML.Trans.ToGraph
import IML.Trans.FromGraph
import IML.Trans.Sanitise
import IML.Trans.ProMan

import Control.Arrow

chain :: Component Program Program
chain = check_bindings >>> uniquify_bindings >>> graphify >>> 
            sequentialise >>> remove_rebindings >>> graphify >>> 
            unify_bindings >>> remove_common_rewrites
