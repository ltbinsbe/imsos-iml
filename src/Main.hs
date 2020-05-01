
module Main where

import IML.Trans.ProMan 
import IML.Trans.Unite
import IML.CodeGen.LaTeX
import IML.CodeGen.LaTeXModule
import IML.CodeGen.RascalModule
import IML.Grammar.Mixed
import IML.Lexer
import IML.Parser
import IML.Printer
import IML.Interpreter.HighInterpreter (program2output)

import Control.Arrow ((>>>))
import Data.List (isSuffixOf, partition)

import System.Environment

main = getArgs >>= run

run :: [String] -> IO()
run args | null imlfs = putStrLn "Please provide some .iml files in the arguments" 
         | otherwise  = selectPipeline imlfs options 
  where (imlfs,options) = partition (".iml" `isSuffixOf`) args 

selectPipeline :: [FilePath] -> [String] -> IO ()
selectPipeline imlfs options
  | "--LaTeX" `elem` options = 
      execProgram imlfs options program2latex_module >>= print_latex_module options
  | "--high" `elem` options = 
      execProgram imlfs options program2highstring >>= putStr
  | "--run" `elem` options =
      execProgram imlfs options (program2output options) >>= id
  | "--rascal" `elem` options = 
      execProgram imlfs options program2rascal_module >>= print_rascal_module options
  | otherwise = selectPipeline imlfs ("--run" : options)
{-      execProgram imlf options (chain_default >>> chain options) 
        >>= backend imlf options -}

execProgram :: [FilePath] -> [String] -> Component MixedProgram b -> IO b
execProgram fps opts chain = 
  mapM readFile fps >>= runComponentIO (IML.Trans.ProMan.runOptions opts) 
                  (     componentMap (lexer >>> parser) 
                    >>> unites 
                    >>> chain)
{-
chain :: [String] -> Component Program Program 
chain options 
  | "--unify-only" `elem` options   = IML.Trans.UniChain.chain 
  | "--basic-left-factor" `elem` options = IML.Trans.ChainBasicLeftFactor.chain
  | "--left-factor" `elem` options  = IML.Trans.ChainLeftFactor.chain
  | "--full-reorder-factor" `elem` options = 
      IML.Trans.ChainReorderFactor.chain >>> IML.Trans.ChainReorder.chain
  | "--reorder" `elem` options      = IML.Trans.ChainReorder.chain
  | otherwise                       = IML.Trans.Chain0.chain

backend :: FilePath -> [String] -> Program -> IO () 
backend imlf options 
  | "--interpret" `elem` options = printer outf options . runProgram options
--  | "--haskell" `elem` options = printer hsf options . hs_print options
  | "--iml" `elem` options = printer modf options . iml_print
  | "--all" `elem` options = \program -> do 
--      writeFile hsf (hs_print options program)
      writeFile outf (runProgram options program)
      writeFile modf (iml_print program) 
  | otherwise = printer outf options . runProgram options
  where
  printer :: FilePath -> [String] -> String -> IO ()
  printer file options 
    | "--write-file" `elem` options = writeFile file 
    | otherwise = putStrLn 
  hsf = replaceExtension imlf "hs"
  outf = replaceExtension imlf "output"
  modf = replaceBaseName imlf (takeBaseName imlf ++ "_mod")

--hs_print options = 
--  print_hs_module . program2hs (IML.Options.runOptions options) 
runProgram options = 
  unlines . map (INTERPRETER.showQRes options) . INTERPRETER.run  
-}
