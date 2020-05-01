
module IML.Grammar.Mixed (
  module IML.Grammar.Shared,
  module IML.Grammar.Low,
  module IML.Grammar.High,
  MixedProgram, MixedDecl, MixedSpec) where

import IML.Grammar.Low
import IML.Grammar.Shared 
import IML.Grammar.High
import IML.Grammar.Specs
import IML.Grammar.Programs

-- A mixed program is some queries + a mixture of:
--    * an inference rule 
--    * single-branched transactions
type MixedProgram = AProgram MixedDecl 
type MixedSpec    = Spec MixedDecl 
type MixedDecl    = Either Rule ProcDecl

