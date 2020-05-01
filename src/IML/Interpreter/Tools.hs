
module IML.Interpreter.Tools where

import IML.Grammar
import IML.Options
import IML.Printer
import qualified IML.Interpreter as IP

import Text.PrettyPrint.HughesPJ

import Control.Monad (when)

import System.FilePath

printFiles :: [String] -> FilePath -> Int -> Program -> IO ()
printFiles args imlFile i pr = do
  writeFile outFile manipulated_version 
  writeFile resFile outcome
  when (any (== "--debug") args) (putStrLn outcome)
  where outFile = replaceExtension imlFile "siml" 
        resFile = replaceExtension imlFile "output" 
        (path,ext) = splitExtension imlFile
        outcome = unlines $ map (IP.showQRes args) $ IP.run pr 

        manipulated_version = iml_print pr

