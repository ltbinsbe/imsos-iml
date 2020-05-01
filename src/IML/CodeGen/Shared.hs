
module IML.CodeGen.Shared where

import Prelude hiding ((<>))

import Text.PrettyPrint.HughesPJ

import Data.List(intersperse)

vsep = vcat . intersperse (text "")
dq = doubleQuotes . text
gString = dq 

csd :: [Doc] -> Doc
csd = hcat . punctuate comma

gRecord :: [Doc] -> Doc
gRecord = braces . csd

gList :: [Doc] -> Doc
gList = brackets . csd

gTuple :: [Doc] -> Doc
gTuple = parens . csd

gSeq :: (Doc -> Doc) -> (a -> Doc) -> [a] -> Doc
gSeq _ gen [a] = gen a
gSeq delimit gen as = delimit $ hcat $ intersperse comma $ map gen as 
 
d1 <<$>> d2 = d1 <+> text "<$>" <+> d2
d1 <=> d2 = d1 <+> text "=" <+> d2
d1 <->> d2 = d1 <+> text "->" <+> d2
d1 <<-> d2 = d1 <+> text "<-" <+> d2
d1 <.> d2 = d1 <> text "." <> d2
d1 <--> d2 = d1 <> text "_" <> d2

gBool :: Bool -> Doc
gBool = text . show 
mkLet p def = text "let" <+> p <=> def
mkLookup k m = m <+> text "M.!" <+> k 
mkInsert op k v m = text op <+> k <+> parens v <+> m
mkMaybe no yes s = text "maybe" <+> no <+> yes <+> parens s
mkLam vars body = parens (text "\\" <> vars <->> body)
mkReturn body = text "return" <+> parens body

ppEither :: (a -> Doc) -> (b -> Doc) -> Either a b -> Doc
ppEither f _ (Left a) = f a
ppEither _ f (Right a) = f a

repHyphen [] = []
repHyphen ('-':xs) = '_':repHyphen xs
repHyphen (x:xs) = x:repHyphen xs

repUnderscore [] = []
repUnderscore ('_':xs) = '-':repUnderscore xs
repUnderscore (x:xs) = x:repUnderscore xs

escUnderscore [] = []
escUnderscore ('_':xs) = "\\_"++escUnderscore xs
escUnderscore (x:xs) = x:escUnderscore xs
