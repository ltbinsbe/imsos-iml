
module IML.Grammar.Programs where

import IML.Grammar.High
import IML.Grammar.Specs

data Interaction  = DoQuery Query
                  | ResetEnv
data Query        = Query Premise [VarDecl]

type Program      = LowProgram
type LowProgram   = AProgram ProcDecl
type HighProgram  = AProgram Rule

data AProgram t   = Program (Spec t) [Interaction]

instance Functor AProgram where
  fmap f (Program s q) = Program (fmap f s) q

instance Foldable AProgram where
  foldMap f (Program s q) = foldMap f s

instance Traversable AProgram where
  traverse f (Program s q) = Program <$> traverse f s <*> pure q


