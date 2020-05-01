{-# LANGUAGE LambdaCase #-}

module IML.Trans.LeftFactor where

import IML.Grammar.Bindings
import IML.Grammar.Low
import IML.Trans.ProMan

import Control.Monad

left_eq_factor, left_factor :: Traversable t => Component (t [Stmts]) (t [Stmts])
left_eq_factor = left_factorA eq_unify
left_factor = left_factorA unify_with_bias

left_factorA :: Traversable t => (Stmt -> Stmt -> ProMan (Maybe SubsEnv)) -> 
                                    Component (t [Stmts]) (t [Stmts])
left_factorA unify = component (traverse branches)
  where branches :: [Stmts] -> ProMan [Stmts]
        branches bss = lfactor unify Branches unbranch bss >>= \case
                        [Branches sss] -> return sss
                        ss             -> return [ss]
          where unbranch s = case s of  Branches sss  -> Just sss
                                        _             -> Nothing 
                        

eq_unify :: (Eq a) => a -> a -> ProMan (Maybe SubsEnv) 
eq_unify x y | x == y     = return (Just subsEmpty)
             | otherwise  = return Nothing

lfactor :: (HasMVar a, Ord a) => 
  (a -> a -> ProMan (Maybe SubsEnv)) ->   -- unification operator (left-biased)
  ([[a]] -> a) ->                         -- branching function
  (a -> Maybe [[a]]) ->                   -- unbranching function
  [[a]] ->                                -- zero or more sequences 
  ProMan [a]                              -- factorisation `tree`
lfactor _ _ _ [] = return []
lfactor unify branch unbranch (ss:sss) = foldM add ss sss
  where
    add [] _ = error "add applied to empty factorisation tree"
    add tree [] = return tree
    -- invariant 0: seq does not contain any branching nodes
    add tree@(current:tree') seq@(s:ss) = case unbranch current of
      Nothing -> current `unify` s >>= \case
                    Nothing   -> return [branch [tree,seq]]
                    Just env  -> (current :) <$> add tree' (sub_mvars env ss)
      -- invariant 1: if `current` is a branching node, then `tree' == []`
      Just []   -> error "empty branching!"
      Just brs  -> -- find single immediate child that unifies with `s`
                   -- relying on the fact that `unify` is a symmetric and
                   -- transitive relation
                   -- restricted to consider last branch only,
                   -- in order to preserve original ordering!
                  lookahead s [last brs] >>= \case
                    Nothing           -> return [branch (brs++[seq])]
                    Just (hd,cand,tl) ->
                      do  cand' <- add cand seq
                        -- invariant 2: no two adjacent branching nodes,
                        -- based on `cand` beginning with unifiable statement 
                          return [branch (init brs ++ hd ++ [cand'] ++ tl)]
{-
                    Just (hd,cand,tl) -> 
                        -- invariant 2: no two adjacent branching nodes,
                        -- based on `cand` beginning with unifiable statement 
                        do cand' <- add cand seq
                           return [branch (hd ++ [cand'] ++ tl)]
-}
     where
--      lookahead :: a -> [[a]] -> ProMan (Maybe ([a], [[a]]))
      lookahead s []        = return Nothing
      lookahead s (br:brs)  = unify (head br) s >>= \case
                                Nothing -> do mres <- lookahead s brs
                                              case mres of
                                                Nothing -> return Nothing
                                                Just (hd,cand,tl) -> return $ Just (br:hd,cand,tl)
                                Just _  -> return $ Just ([], br, brs)
