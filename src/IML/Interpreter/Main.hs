
import IML.Interpreter.Lexer
import IML.Interpreter.Parser
import IML.Interpreter.Tools
import IML.Trans.ProMan
import IML.Trans.Chain2 as C

import Data.List

import System.Environment

main :: IO()
main = getArgs >>= selectFile

selectFile :: [String] -> IO ()
selectFile args = 
  case filter (isSuffixOf ".iml") args of
    []          -> putStrLn "Please provide an .iml file"
    (_:(_:_))   -> putStrLn "Please provide a single .iml file"
    [file]      -> run file (filter (isPrefixOf "--") args)

run :: FilePath -> [String] -> IO ()
run fp args = do
  input <- readFile fp
  let prs = iml_parser (iml_lexer input)
  mapM_ (uncurry printFiles') (zip [1..] prs)
    where printFiles' i pr = 
            runComponentIO opts C.chain pr >>= printFiles args fp i
          opts = runOptions args


