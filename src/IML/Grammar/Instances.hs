{-# LANGUAGE StandaloneDeriving #-}

module IML.Grammar.Instances where

import IML.Printer ()
import IML.Grammar
import IML.Trans.Graphs

deriving instance Show a => Show (AProgram a)
deriving instance Show Query 
deriving instance Show Stmt 
deriving instance Show Pattern
deriving instance Show Expr 
deriving instance Show Rep 
deriving instance Show Rel 
deriving instance Show RelDecl 
deriving instance Show EntDecl
deriving instance Show a => Show (ATransDecl a)
deriving instance Show a => Show (AnyDecls a)
deriving instance Show a => Show (Graph a)
deriving instance Show a => Show (ASpec a)


