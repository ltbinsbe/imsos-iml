
module IML.Trans.ChainBasicLeftFactor where

import IML.Grammar
import IML.Trans.Bindings
import IML.Trans.LeftFactor
import IML.Trans.ProMan

import Control.Arrow

chain :: Component Program Program 
chain = check_bindings >>> left_factor 

