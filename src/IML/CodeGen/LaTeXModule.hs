
module IML.CodeGen.LaTeXModule where

import Prelude hiding ((<>))

import Data.List(intersperse)
import Text.PrettyPrint.HughesPJ

import Data.List (sortBy, groupBy)
import Data.Function (on)

instance Show LaTeXModule where
  show = render_latex_module 

print_latex_module :: [String] -> LaTeXModule -> IO ()
print_latex_module options = putStrLn . rModule

output_latex_module :: LaTeXModule -> IO ()
output_latex_module = putStrLn . rModule

render_latex_module :: LaTeXModule -> String 
render_latex_module = rModule

data LaTeXModule = LaTeXModule {
        lm_doc_class :: String
      , lm_packages  :: [String]
      , lm_fragments :: [(Int, Doc)]
      }

defaultModule :: LaTeXModule 
defaultModule = 
  LaTeXModule "article" ["amsmath","amssymb","mathpartir"] [] 

rModule :: LaTeXModule -> String
rModule = render . ppModule

ppModule :: LaTeXModule -> Doc
ppModule mod = 
  text "\\documentclass" <> braces (text (lm_doc_class mod)) $+$
  vcat [ text "\\usepackage" <> braces (text pack) | pack <- lm_packages mod ] $+$
  text "\\usepackage[margin=1cm]{geometry}" $+$
  text "\\begin{document}" $+$
  vcat ( [
          text "\\begin{gather}" $+$
          vcat (intersperse rulesep rules) $+$
          text "\\end{gather}"
         | rules <- sortedBlocks ]) $+$
  text "\\end{document}"
  where sortedBlocks = map (map snd) $
                          groupBy ((==) `on` fst) $ 
                          sortBy (compare `on` fst) $
                          lm_fragments mod

linesep :: Doc
linesep = text "\\\\"

rulesep :: Doc
rulesep = text "\\\\[3ex]"
