
module IML.Trans.FromGraph where

import IML.Grammar
import IML.Trans.Graphs
import IML.Trans.ProMan

import Data.List (minimumBy)

sequentialise :: Traversable t => Component (t [Graph Stmt]) (t [Stmts])
sequentialise = component_ (fmap (map toProc))

toProc :: Graph Stmt -> Stmts
toProc gr = schedule gr

-- variations of schedule from Trans.Graphs 
schedules_tl :: Graph Stmt -> [Stmts]
schedules_tl gr = schedules' [] gr (entries gr) 
  where schedules' acc gr ents | null ents = [acc]
                               | otherwise = concatMap rec ents
          where rec e = schedules' (acc++[e]) gr' (entries gr')
                  where (gr',_) = deleteWithEntries e gr

schedules :: Graph Stmt -> [Stmts]
schedules gr | null ents = [[]]
             | otherwise = concatMap rec ents 
  where rec e = map (e:) (schedules gr')
                  where (gr',_) = deleteWithEntries e gr
        ents = entries gr

scheduleByOrder :: (Stmts -> Graph Stmt) ->             -- how to make graph?
                      (Graph Stmt -> 
                        Stmt -> Stmt -> Ordering) ->   -- order over statements
                      Graph Stmt ->                     -- dep-graph to schedule
                      Stmts                             -- schedule
scheduleByOrder toGraph compare gr = schedule' gr (entries gr) []
  where schedule' gr [] uset = uset
        schedule' gr [Branches sss] uset = uset ++ [Branches sss']
          where sss' = map (scheduleByOrder toGraph compare . toGraph) sss
        schedule' gr es uset = schedule' gr' (entries gr') (uset ++ [e])
          where (gr',_)   = deleteWithEntries e gr 
                e         = minimumBy (compare gr) es
