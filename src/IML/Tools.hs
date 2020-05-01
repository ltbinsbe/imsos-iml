
module IML.Tools (
  ProMan, ProState, Component, component, component_, runComponent, runComponentIO, 
    runOptions, fresh_var_name, fresh_var_, 
    runWithDefaults, warn, add_csv,
  printIML, 
  module IML.Trans.Graphs,
  ) where

import IML.Trans.ProMan
import IML.Trans.Graphs
import IML.Trans.ToLower
import IML.Grammar.Grammar
import IML.Grammar.RuleFormat 
import IML.Grammar.Shared
import IML.Printer
import qualified IML.Options as OPTS

printIML :: [String] -> FilePath -> Program -> IO ()
printIML args imlFile pr = do
  writeFile imlFile manipulated_version 
  where manipulated_version = iml_print pr

