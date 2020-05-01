
module IML.Trans.WrapSpec where

import IML.Trans.ProMan
import IML.Grammar.Specs
import IML.Grammar.Programs
import IML.Grammar.Mixed

mix_program :: Component Program MixedProgram
mix_program = component_ (\(Program spec qs) -> Program (gSpecR spec) qs)

mix_spec :: Component (Spec Rule) (Spec MixedDecl)
mix_spec = component_ gSpecL

gSpecL :: Spec a -> Spec (Either a b)
gSpecL (Spec ds) = Spec (map (fmap Left) ds)

gSpecR :: Spec b -> Spec (Either a b)
gSpecR (Spec ds) = Spec (map (fmap Right) ds)

wrap_spec :: Component (Spec a) (AProgram a)
wrap_spec = component_ (\spec -> Program spec [])

unwrap_spec :: Component (AProgram a) (Spec a)
unwrap_spec = component_ gProgram
  where gProgram (Program spec qs) = spec

 
