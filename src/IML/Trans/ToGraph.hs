{-# LANGUAGE FlexibleInstances #-}

module IML.Trans.ToGraph where

import IML.Grammar
import IML.Grammar.Bindings
import IML.Trans.Graphs
import IML.Trans.ProMan
import IML.Trans.FromGraph (scheduleByOrder)

import Data.List (minimumBy)
import qualified Data.Set as S

graphify :: Functor t => Component (t [Stmts]) (t [Graph Stmt])
graphify = component_ (fmap (map toGraph))

reorder :: Functor t => Component (t [Stmts]) (t [Stmts])
reorder = component_ (fmap (map (scheduleByOrder toGraph' ordering . toGraph)))
  where ordering gr x y = case compare (expectedCostOf x) (expectedCostOf y) of
          EQ    -> case (succs x gr, succs y gr) of
                    ([],[]) -> EQ
                    (_,[])  -> LT
                    ([],_)  -> GT
                    (xs,ys) -> ordering gr 
                                (minimumBy (ordering gr) xs) 
                                (minimumBy (ordering gr) ys)
          diff  -> diff
        toGraph' = toGraphWithProf (prof_1 ++ [branching_last])

-- | Compute a dependency graph from a branch.
-- Potentially costly, as many dependencies may be inserted.
toGraph :: Stmts -> Graph Stmt
toGraph = toGraphWithProf prof_1

toGraphWithProf :: DepProfile -> Stmts -> Graph Stmt
toGraphWithProf profile ss = inserts es (initialise ss)
  where es = dependencies profile ss

-- dependency profiles
type DepProfile = [Stmt -> Stmt -> Bool]

dependencies :: DepProfile -> Stmts -> [(Stmt, Stmt)]
dependencies prof ss = filter pred (allPairs ss)
  where pred args = or $ map (($ args) . uncurry) prof

prof_0    = [binds_for, sets_for, from_gets {-, pre_unobs-} ]
prof_1    = prof_0 ++ [commit_last] 
set_get_0 = [get0, set0]
prof_all  = prof_0 ++ set_get_0 ++ [commit_last]

-- | Decide whether the first statement binds a meta-variable
-- that is required by the second statement
binds_for :: Stmt -> Stmt -> Bool
binds_for f t = not $ S.null $ pvars_set f `S.intersection` tvars_set t

-- | Decide whether the first statement sets an entity value
-- required by the second statement
sets_for :: Stmt -> Stmt -> Bool
sets_for f t = case f of 
      Set _ _ l  -> required l
      _          -> False
    where required l1 = case t of
            Trans _ _ _ l2  -> l1 == l2
            _               -> False

-- | Decide whether the first statements provide an entity value
-- that is obtained by the second statement (second is getter)
from_gets :: Stmt -> Stmt -> Bool
from_gets f t = case f of 
    Trans _ _ _ l -> required l
    _             -> False
  where required l1 = case t of
          Get _ _ l2 -> l1 == l2
          _          -> False

-- | Getters with label 0 should precede every other statement 
-- with a label greater than 0
get0 :: Stmt -> Stmt -> Bool
get0 (Get _ _ 0) s | Just l <- labelOf s, l > 0 = True
get0 _ _                                        = False

-- | Setters with label 0 should follow every other statement
-- with a label greater than 0
set0 s (Set _ _ 0) | Just l <- labelOf s, l > 0 = True
set0 _ _                                        = False

{-
-- | Decide whether the first statement should preceed the second
-- statement if the second statement is `unobs`
pre_unobs :: Stmt -> Stmt -> Bool
pre_unobs s (Unobserv l) = maybe False (==l) (sLabel s)
  where   sLabel :: Stmt -> Maybe Label
          sLabel (Trans _ _ _ ml) = ml
          sLabel (Get _ _ l)      = Just l
          sLabel _ = Nothing
pre_unobs _ _ = False  
-}

-- | Ensure that commits are always executed last
commit_last :: Stmt -> Stmt -> Bool
commit_last s (Commit _ _) = True
commit_last _ _ = False

-- | Ensure that branches are always last
branching_last s (Branches _) = True
branching_last _ _ = False
