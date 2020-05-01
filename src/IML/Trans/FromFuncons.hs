{-# LANGUAGE OverloadedStrings #-}

module IML.Trans.FromFuncons where

import Funcons.EDSL (Funcons(..),FTerm(..),Values(..),Types(..), SeqSortOp(..), ComputationTypes(..), isString_, unString)
import Funcons.RunOptions (RunOptions(..))
import IML.Grammar 
import IML.Grammar as IML 
import IML.Grammar.Programs (Query(..))
import qualified Funcons.Operations as T

import qualified Data.Map as M
import Data.Text (pack,unpack)
import qualified Data.Set as S
import qualified Data.MultiSet as MS
import Data.String(fromString)

res_var = "Result"

mkQueryFromFCT :: Funcons -> [String] -> Query
mkQueryFromFCT fct ents = Query prem (mkVarDecls ents) 
          where prem = Prem [] (TConf [ETerm $ translate fct] []) "->*"
                               (PConf [PVar res_var] (zipWith op [1..] ents))
                  where op i nm = (nm, [PVar (mkVar i nm)])

mkQuery :: RunOptions -> Maybe Query
mkQuery runopts = fmap mkQuery' (mfuncon_term runopts)
  where mkQuery' fct = Query prem (mkPatDecls (result_term runopts) ents)
          where prem = Prem [] (TConf [ETerm $ translate fct] []) "->*"
                               (PConf [PVar res_var] (map (\(x,v,_) -> (x,[PVar v])) ents))
        ents = zipWith op [1..] $ M.assocs (M.delete "result-term" (expected_outcomes runopts))
          where op i (nm,vs) = (unpack nm, mkVar i vs, vs)

result_term opts = expected_outcomes opts M.! "result-term"

mkVar i e = "Q" ++ show i
mkVarDecls ents = 
  VarDecl res_var 0 Nothing Longest [] : zipWith ((mkVarDecl .) . mkVar) [1..] ents
  where mkVarDecl var = VarDecl var 0 Nothing Longest []
mkPatDecls res ents = 
  VarDecl res_var 0 Nothing Longest 
    [Left $ Prem [] (TConf (map (ETerm . translate) res) []) "~>*" 
                    (PConf [PVar (res_var ++ "'")] [])
    ,Right $ SideOP [VOP "is-equal" [IML.ETerm (IML.TVar res_var)
                                    ,IML.ETerm (IML.TVar (res_var ++ "'"))]] 
                    [IML.PVal (T.ADTVal "true" [])]] : 
      map mkVarDecl ents
  where mkVarDecl (nm,var,pats) = VarDecl var 0 Nothing Longest 
          [Left $ Prem [] (TConf (map (ETerm . translate) pats) []) "~>*"
                          (PConf [PVar (var ++ "'")] [])
          ,Right $ SideOP [VOP "is-equal" [IML.ETerm (IML.TVar res_var)
                                    ,IML.ETerm (IML.TVar (res_var ++ "'"))]] 
                          [IML.PVal (T.ADTVal "true" [])]]

translate :: Funcons -> Term
translate fct = case fct of 
  FName nm                -> TCons (unpack nm) []
  FApp nm fs              -> TCons (unpack nm) (map translate fs)
  FSet fs                 -> TCons "set" (map translate fs)
  FMap kvs                -> TCons "map" (map translate kvs)
  FValue v | isString_ v  -> TVal (fromString (unString v))
           | otherwise    -> TVal (T.vmap translate v)
  FSortSeq ty op          -> TCons ("ty" ++ translate_seqop op) [translate ty]
  FSortPower ty n         -> TCons "typower" [translate ty, translate n]
  FSortUnion t1 t2        -> TCons "tyunion" [translate t1, translate t2]
  FSortInter t1 t2        -> TCons "tyinter" [translate t1, translate t2]
  FSortComplement ty      -> TCons "tyneg" [translate ty]
  FSortComputes ty        -> TCons "tycomp" [TCons "values" [], translate ty]
  FSortComputesFrom fty ty-> TCons "tycomp" [translate fty, translate ty]
  FBinding tk tvs         -> TCons "tuple" (map translate (tk:tvs))

translate_term :: FTerm -> Term
translate_term (TName "list")     = TVal (T.ADTVal "list" [])
translate_term (TName "tuple")    = TVal (T.ADTVal "tuple" [])
translate_term (TApp "list" xs)   
  | all isTermVal xs = TVal (T.ADTVal "list" (map translate_term xs))
translate_term (TApp "tuple" xs) 
  | all isTermVal xs = TVal (T.ADTVal "tuple" (map translate_term xs))
translate_term (Funcons.EDSL.TVar v) = IML.Grammar.TVar (remVarOp v)
translate_term (TName nm)   = TCons (unpack nm) []
translate_term (TApp nm ts) = TCons (unpack nm) (map translate_term ts)
translate_term (TSet ts)    = TCons "set" (map translate_term ts)
translate_term (TBinding tk tvs) = TCons "tuple" (translate_term tk : translate_terms tvs)
translate_term (TMap ts) = TCons "map" (map translate_term ts)
translate_term (TFuncon f) = translate f 
translate_term (TSortSeq t op) = TCons ("ty" ++ translate_seqop op) [translate_term t]
translate_term (TSortPower t1 n) = TCons "typower" [translate_term t1, translate_term n]
translate_term (TSortUnion t1 t2) = TCons "tyunion" [translate_term t1, translate_term t2]
translate_term (TSortInter t1 t2 )  = TCons "tyinter" [translate_term t1, translate_term t2]
translate_term (TSortComplement ty) = TCons "tyneg" [translate_term ty] 
translate_term (TSortComputes t1) = TCons "tycomp" [TCons "values" [], translate_term t1]
translate_term (TSortComputesFrom t1 t2) = TCons "tycomp" [translate_term t1, translate_term t2]
translate_term TAny = TCons "values" []
translate_term (TSeq _) = error "sequence encountered in translation"

translate_terms :: FTerm -> [Term]
translate_terms (TSeq ts) = concatMap translate_terms ts
translate_terms t         = [translate_term t]

translate_seqop :: SeqSortOp -> String
translate_seqop StarOp          = "star"
translate_seqop PlusOp          = "plus"
translate_seqop QuestionMarkOp  = "opt"

remVarOp :: String -> String 
remVarOp [] = []
remVarOp cs | c == '*' = init cs ++ "s"
            | c == '?' = init cs ++ "q"
            | c == '+' = init cs ++ "p"
            | otherwise= cs
  where c = last cs

isTermVal :: FTerm -> Bool
isTermVal (TFuncon (FValue v)) = True
isTermVal _ = False
