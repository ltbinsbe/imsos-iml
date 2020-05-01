
module IML.Trans.Chain1 where

import IML.Grammar
import IML.Trans.ToGraph
import IML.Trans.FromGraph
import IML.Trans.ProMan

import Control.Arrow

chain :: Component Program Program
chain = graphify >>> sequentialise
