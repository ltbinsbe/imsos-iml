
-- | 
-- Haskell module for uniting two (or more) mixed IML programs
-- The union is obtained by uniting the individual components of IML programs:
--   (assumes no entity or relation is declared more than once)
--
--  * queries : unite collection of queries
--  * declarations 
--      * terminal constructor/builtin: 
--            unite collections of (relation symbol * cons/builtin) pairs
--      * entity (default): unite sets of (eid * expr) pairs
--          assumes no conflicts, i.e. union of pairs forms a mapping
--      * relation (flags): unite (relation symbol * flags) pairs
--          assumes no conflicts, i.e. union of pairs forms a mapping
--      * rules: unite collections of rules
--      * procedures: unites collection of procedure declarations
--          /without/ merging the branches of procedures with identical signatures
module IML.Trans.Unite where

import IML.Grammar.High
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Grammar.Mixed
import IML.Trans.ProMan

unites :: Component [MixedProgram] MixedProgram
unites = component_ (foldr unitePrograms (Program (Spec []) []))

unite :: Component (MixedProgram, MixedProgram) MixedProgram
unite = component_ (uncurry unitePrograms)

unitePrograms :: MixedProgram -> MixedProgram -> MixedProgram
unitePrograms (Program (Spec ds1) qs1) 
              (Program (Spec ds2) qs2) = 
              (Program (Spec (ds1 ++ ds2)) (qs1 ++ qs2))

