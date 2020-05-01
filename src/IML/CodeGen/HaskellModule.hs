
module IML.CodeGen.HaskellModule where

import IML.Grammar hiding (Queries)
import IML.CodeGen.Shared

import Text.PrettyPrint.HughesPJ

import Data.Char (isUpper, toLower)
import Data.List (intersperse)
import qualified Data.Map as M

-- | Haskell function names
type FunName  = String 
-- | Haskell module name
type ModName  = [String]
-- | Haskell imports
type Imports  = [Either String {- literal string representing imports -}
                        (ModName, Maybe String {- maybe qualified name -})]
-- | Haskell language extensions
type Exts     = [String]
-- | Haskell function definition
type HSDef    = (FunName, Doc)

-- |
-- Representation of Haskell modules
data HaskellModule = HaskellModule {
                        hs_modname      :: (Maybe ModName)
                      , hs_imports      :: Imports
                      , hs_extensions   :: Exts 
                      , hs_entity_defs  :: Entities  --    Dir   |-> (EID, (FunName, Doc))
                      , hs_rel_defs     :: Relations --    RSymb |-> (Cons, (FunName, Doc))
                      , hs_query_defs   :: Queries   --    [(FunName, Doc)] 
                      , hs_aux_defs     :: [HSDef]   --    auxiliary functions
                        }

type Entities   = M.Map Dir [(EID, HSDef)]
type Relations  = M.Map RSymb [(Cons, HSDef)]
type Queries    = [HSDef]

add_direct_import :: String -> HaskellModule -> HaskellModule
add_direct_import str mod = mod { hs_imports = hs_imports mod ++ [Left str] }
add_expl_import   :: (ModName, Maybe String) -> HaskellModule -> HaskellModule
add_expl_import imp mod = mod { hs_imports = hs_imports mod ++ [Right imp] }

set_modname :: ModName -> HaskellModule -> HaskellModule
set_modname nm mod = mod { hs_modname = Just nm }

print_hs_module :: HaskellModule -> String
print_hs_module (HaskellModule mn is exts es rs qs rest) = 
 render $ vsep $
  [text "{-#" <+> text "LANGUAGE" <+> csd (map text exts) <+> text "#-}"] ++
  [text "module" <+> ppModName name <+> text "where"] ++ 
  [vcat (map ppImport is)] ++
  [ d | decls <- M.elems es, (_,(f,d)) <- decls ] ++
  [ d | css <- M.elems rs, (c,(f,d)) <- css ] ++
  [vcat [ d | (f,d) <- qs ] ] ++ 
  [ d | (f,d) <- rest ] 
  where name = maybe ["Main"] id mn

ppModName :: ModName -> Doc
ppModName xs = hcat $ intersperse (text ".") (map text xs)

ppImport :: Either String (ModName, Maybe String) -> Doc
ppImport (Left str) = text str
ppImport (Right (nm,mq)) = ppImport' nm mq
  where
    ppImport' :: ModName -> Maybe String -> Doc
    ppImport' xs Nothing = text "import" <+> ppModName xs
    ppImport' xs (Just qal) = 
      text "import" <+> text "qualified" <+> ppModName xs <+> text "as" <+> text qal

hsVar :: MVar -> Doc
hsVar = text . lower_hs_name . uncapitalise . show

uncapitalise :: String -> String
uncapitalise = map uncap
 where uncap c  | isUpper c = toLower c
                | otherwise = c

lower_hs_name :: String -> String
lower_hs_name = map unhypen
  where unhypen '-' = '_'
        unhypen c   = c 
