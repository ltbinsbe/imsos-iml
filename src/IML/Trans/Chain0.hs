
module IML.Trans.Chain0 where

import IML.Grammar.Programs
import IML.Trans.ProMan

chain :: Component Program Program
chain = component_ id
