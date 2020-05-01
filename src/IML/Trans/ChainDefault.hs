
module  IML.Trans.ChainDefault where

import IML.Grammar.Mixed
import IML.Trans.ProMan
import IML.Trans.RelFlags
import IML.Trans.Unmix
import IML.Trans.Bindings

import Control.Arrow

chain_default :: Component MixedProgram Program
chain_default = rules_from_flags >>> unmix >>> check_bindings 
