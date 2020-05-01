{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module IML.Interpreter.Types where

import IML.Grammar.Shared
import IML.Grammar
import IML.Grammar.Specs
import IML.CodeGen.Shared
import IML.Printer (ppTConf)
import IML.Operations (library)

import Funcons.Operations(Values(ADTVal,ComputationType,ValSeq), ComputationTypes(Type), Types(ADT), libAppWith, EvalResult(..),eval, OpExpr(ValExpr,TermExpr),Result(..))

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM
import Data.Text (unpack)
import Data.Maybe (fromJust, isJust)
import Data.Tree
import Text.PrettyPrint.HughesPJ

import Control.Arrow ((***))
import Control.Monad (forM)

-- interpreter types

type Specf = (RuleColl Rule, GlobMap Rule, RelTable, ConsSet, Record {-contexts's-})
type State = (MetaEnv, Record, [Deriv])
type Varf  = M.Map MVar VarDecl
type Conf = ([Term] {- closed -}, Record)

data StmtValue = Nil | Bot | Res ([Term] {-closed-}, Record)
isBot :: StmtValue -> Bool
isBot Bot = True
isBot _   = False

sem_spec :: Spec Rule -> Specf
sem_spec (Spec ds) = (tm, gr, rt, css, e0)
  where
   (eds,tcons,relds,vardecls,transds) = partition_decls ds
   (tm,gr) = foldr eRuleDecl (transEmpty,globEmpty) transds
   css = foldr eTConsDecl M.empty tcons 
   rt = relFromDecls relds
   e0 = foldr (eEntDecl css) recEmpty eds

eTConsDecl :: TConsDecl -> ConsSet -> ConsSet
eTConsDecl (PCTerm rsymb elr) = M.insertWith S.union rsymb (S.singleton elr)   
eTConsDecl (EIDTerm eid elr) = M.insertWith S.union eid (S.singleton elr)

eRuleDecl :: Rule -> (RuleColl Rule, GlobMap Rule) -> (RuleColl Rule, GlobMap Rule)
-- assumes merging of global rules has already taken place
eRuleDecl rule@(Rule prio (Concl _ (PConf ps _) rel (TConf es _)) scs vds) (tm,gr) = 
  case mkStaticPattern (mkVarMap vds) ps of 
    Right pat -> (transAdd rel pat prio rule tm, gr)
    Left i    -> (tm, globAdd rel i prio rule gr)

eEntDecl :: ConsSet -> EntDecl -> Record -> Record
eEntDecl css (EntDecl eid ss) rec = recInsert eid (evalDef ss) rec
    where evalDef e = case eExprs e of
                        Nothing -> error "failed to evaluate to default value"
                        Just vs -> vs
 
-- information about (sequence) variables

type MetaEnv  = M.Map MVar [Term] 
envEmpty :: MetaEnv
envEmpty      = M.empty
envUnite :: MetaEnv -> MetaEnv -> MetaEnv
envUnite      = flip M.union
bind :: MVar -> [Term] -> MetaEnv
bind          = M.singleton
--binds xs ts   = matches (M.empty, const Just) ts (map PVar xs)

-- expression evaluation

type ExprRes = Maybe [Term] {- closed terms -}

eExprs :: [Expr] -> ExprRes
eExprs es = concat <$> mapM eExpr es

eExpr :: Expr -> ExprRes
eExpr e = case e of
  ETerm t -> Just [t]
  VOP vop es -> let mts = map eExpr es in case all isJust mts of
    True  -> myLibApp vop (concatMap fromJust mts)
    False -> Nothing 
 where  myLibApp vop ts = mkValExpr e >>= \ex -> case eval ex of 
          Error _ (DomErr _)                -> Just []
          Error _ _                         -> Nothing
          -- arbitrary terms are wrapped and unwrapped as thunks
--          Success (TVal (ADTVal "null" _))  -> Just []
          Success (TVal (ValSeq vs))        -> Just vs
          Success v                         -> Just [v] 

        mkValExpr e = case e of
          ETerm t -> case t of TVal v  -> Just (ValExpr v)
                               _       -> Just (TermExpr t)
          VOP vop' es -> case all isJust es' of
                          True  -> case libAppWith library libkey (map fromJust es') of
                                    Nothing -> error ("not found: " ++ libkey ++ " with arity " ++ (show (length es')))
                                    Just ex -> Just ex
                          _     -> Nothing
            where es' = map mkValExpr es
                  libkey = repUnderscore vop'

eval_conf :: Record -> TConf -> Maybe Conf
eval_conf rec0 (TConf es ents) = do
  ts <- eExprs es
  ents' <- forM ents $ \(e,ex) -> do
    t <- eExprs ex 
    return (e,t)
  let rec1 = foldr (uncurry M.insert) rec0 ents'
  return (ts, rec1)

-- representing derivations
type Deriv = Tree Transition
data Transition = Transition { lhs :: Conf
                             , rel :: RSymb
                             , rhs :: Conf
                             , mentioned_entities :: [EID] }

root :: Deriv -> Transition
root = rootLabel

mkDeriv :: Conf -> RSymb -> Conf -> [EID] -> [Deriv] -> Deriv
mkDeriv l rel r ents = Node (Transition l rel r ents)

showTrans :: Transition -> String
showTrans (Transition lconf@(ts1,rec1) r rconf@(ts2,rec2) ents) =
  showConf lconf ++ " " ++ r ++ " " ++ showConf rconf 
  where showConf (ts,rec) = let ?repHyphen = id in render $ ppTConf $ 
            TConf (map ETerm ts) 
                  (map (id *** map ETerm) (filter mentioned (M.assocs rec)))
          where mentioned (e,v) = e `elem` ents
 
-- entity storage

-- mapping from entity id to its default value
type DefF = EID -> [Term]

type Record = M.Map EID [Term]

recEmpty :: Record
recEmpty = M.empty

recNull :: Record -> Bool
recNull = M.null

recAdjust :: EID -> [Term] -> Record -> Record
recAdjust eid t = M.adjust (\_ -> t) eid 

recInsert :: EID -> [Term] -> Record -> Record
recInsert = M.insert

-- right-biased record union
recUnite :: Record -> Record -> Record
recUnite = flip M.union

recUnites :: [Record] -> Record
recUnites = foldr recUnite recEmpty 

recDel :: EID -> Record -> Record
recDel = M.delete

entValue :: Record -> EID -> Maybe [Term]
entValue = flip M.lookup

-- transaction alternatives

type RuleColl r = IM.IntMap [(RSymb, [StaticPattern], r)]

transEmpty = IM.empty

transAdd :: RSymb -> [StaticPattern] -> Int -> r -> RuleColl r -> RuleColl r
transAdd rel c pr branch = IM.insertWith (++) pr [(rel, c, branch)]

-- returns all branches to be executed for the given relation symbol
-- and constructor sequence. 
-- The sequence of constructors should match the sequence of static patterns
-- Each branch is paired with its priority
transOf :: RSymb -> [Term] -> RuleColl r -> [(Int, r)]
transOf r cs = concatMap unGroup . map filterMatches . IM.assocs
  where unGroup (k, vss) = map (\(r,ps,ss) -> (k,ss)) vss
        filterMatches (k, es) = (k, filter isMatch es)
          where isMatch (r', ps, ss) =  r == r'
                                    &&  length cs == length ps 
                                    &&  and (zipWith static_match cs ps)

static_match :: Term -> StaticPattern -> Bool
static_match _ (NoCons i _)                       = True
static_match (TCons c _) (TeCons c')              = c == c'
static_match (TVal (ADTVal c _)) (VaCons c')      = unpack c == c'
static_match (TVal (ComputationType (Type (ADT c _)))) (TyCons c')  = unpack c == c'
static_match _ _                                  = False

-- alternatives that are generally applicable 
--  (not restricted to a particular cons)
-- they are subject to priorities
type GlobMap r = M.Map RSymb (IM.IntMap [(r, Int {- static pattern -})])

globEmpty = M.empty

globAdd :: RSymb -> Int {- min length of seq -} -> Int -> r -> GlobMap r -> GlobMap r
globAdd r pat c ss = M.alter op r
  where op Nothing  = Just $ IM.singleton c [(ss,pat)]
        op (Just m) = Just $ IM.insertWith (++) c [(ss,pat)] m

-- returns all branches to be executed for the given relation symbol.
-- Each branch is paired with its priority
globOf :: RSymb -> [Term] -> GlobMap r -> [(Int, r)] 
globOf r cs = maybe [] (concatMap unGroup . IM.assocs) . M.lookup r 
  where unGroup (k, vss) = map (k,) (foldr op [] vss)
          where op (r,i) acc | seq_length >= i = r:acc
                             | otherwise       = acc 
        seq_length = length cs
