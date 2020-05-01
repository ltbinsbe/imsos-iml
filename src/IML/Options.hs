
module IML.Options where

data Options = Options  { haskell_patterns :: Bool
                        }

defaultOptions = Options False

runOptions :: [String] -> Options
runOptions = foldr op defaultOptions 
  where op "--haskell-patterns" opts = opts {haskell_patterns = True}
        op _ opts = opts
