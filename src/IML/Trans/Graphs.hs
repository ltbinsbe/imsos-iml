{-# LANGUAGE InstanceSigs #-}

module IML.Trans.Graphs (
  Graph (..), showGraph, empty, initialise, 
  succs, preds, entries, nodes, nullEdges, nullNodes, 
  insert, inserts, addEdge, addEdges,
  delete, deleteWithEntries,
  graphMap,
  paths, schedule,
  allPairs 
  ) where

import Data.Maybe (isNothing)
import qualified Data.Map as M
import qualified Data.Set as S

newtype Graph n = Graph
                ( M.Map n (Maybe (S.Set n))  -- successor (Nothing if deleted)
                , M.Map n (Maybe (S.Set n))  -- predecessors (Nothing if deleted)
                )
 
-- | An empty graph
empty :: Graph n
empty = Graph (M.empty, M.empty)

initialise :: (Ord n) => [n] -> Graph n
initialise ns = Graph (M.fromList empts, M.fromList empts)
  where empts = [ (n, Just S.empty) | n <- ns ]

-- | Get the successor of a node in a given graph
succs :: (Ord n) => n -> Graph n -> [n]
succs  n (Graph gr) = maybe [] (maybe [] S.toList) $ M.lookup n (fst gr)

(!>) :: (Ord n) => Graph n -> n -> [n]
(!>) = flip succs

-- | Get the predecessors of a node in a given graph
preds :: (Ord n) => n -> Graph n -> [n]
preds n (Graph gr) = maybe [] (maybe [] S.toList) $ M.lookup n (snd gr)

(<!) :: (Ord n) => Graph n -> n -> [n]
(<!) = flip preds

-- | Check whether the graph has any edges
nullEdges :: Graph n -> Bool
nullEdges (Graph (fwd,_)) = all (maybe True null) fwd

nullNodes :: Graph n -> Bool
nullNodes (Graph (fwd, _)) = all isNothing fwd

-- | Create an edge between two nodes in a given graph,
-- keeping the graph closed under transitivity
insert :: (Ord n) => n -> n -> Graph n -> Graph n
insert n1 n2 gr = addEdges ((n1,n2):pairs) gr
  where   pairs = [ (f,t) | f <- preds n1 gr, t <- succs n2 gr ]

-- | Create an edge between all given pairs of nodes,
-- keeping the graph closed under transitivity
inserts :: (Ord n) => [(n,n)] -> Graph n -> Graph n
inserts es gr = foldr (uncurry insert) gr es 

-- | Create an edge between two nodes, disregarding transitivity
addEdge :: (Ord n) => n -> n -> Graph n -> Graph n
addEdge n1 n2 (Graph (fwd,bwd)) = Graph $
  (M.insertWith mappend n1 (Just (S.singleton n2)) fwd
  ,M.insertWith mappend n2 (Just (S.singleton n1)) bwd)

-- | Create an edge between all pairs of nodes, disregarding transitivity
addEdges :: (Ord n) => [(n,n)] -> Graph n -> Graph n
addEdges ps gr = foldr (uncurry addEdge) gr ps

-- | Get the nodes of the given graph
nodes :: Graph n -> [n]
nodes (Graph (fwd,_)) = M.foldrWithKey sel [] fwd
  where sel k Nothing acc = acc
        sel k _ acc       = k:acc

-- | Get the entry points of the graph
entries :: Graph n -> [n]
entries (Graph (_,bwd)) = M.foldrWithKey sel [] bwd
  where sel k (Just ns) acc   | null ns     = k:acc
                              | otherwise   = acc
        sel _ _ acc = acc

-- | Deletes a node from a graph
-- by removing all the edges in which it is involved
delete :: (Ord n) => n -> Graph n -> Graph n
delete = (fst .) . deleteWithEntries 

-- | Deletes a node from the graph,
-- returning the new graph and all nodes that became an entry point by the deletion
-- TODO returned entries are not complete!
deleteWithEntries :: (Ord n) => n -> Graph n -> (Graph n, [n])
deleteWithEntries f gr@(Graph (fwd, bwd)) = (gr', newEntries)
  where   fwd'        = M.map (fmap (S.delete f)) (M.insert f Nothing fwd)
          bwd'        = M.map (fmap (S.delete f)) (M.insert f Nothing bwd)
          gr'         = Graph (fwd', bwd')
          newEntries  = filter pred (succs f gr)
            where pred t = null (preds t gr') 

-- | Map a function over all nodes of a graph 
graphMap :: Ord b => (a -> b) -> Graph a -> Graph b
graphMap f (Graph (fwd,bwd)) = Graph $
    (M.mapKeys f (fmap (fmap (S.map f)) fwd)
    ,M.mapKeys f (fmap (fmap (S.map f)) bwd)
    )
    
showGraph :: Show n => Graph n -> String
showGraph (Graph (fwd,_)) = unlines (map op (M.toList fwd))
  where op (f, Nothing) = show f ++ " |--> _"
        op (f, Just ts) | null ts   = show f ++ " |--> []"
                        | otherwise = unlines [ show f ++ " |--> " ++ show t 
                                              | t <- S.toList ts ]

-- | Return all the paths in this graph 
paths :: (Ord n) => Graph n -> [[n]]
paths g = paths' (entries g)
  where paths' [] = [[]]
        paths' vs = concatMap op vs
            where op v = map (v:) $ paths' (succs v g)

-- | Return all nodes in the graph such that if `a -> b` in the graph
-- then `a` occurs before `b` in the result
schedule :: (Ord a) => Graph a -> [a] 
schedule gr = schedule' gr (entries gr) []
  where schedule' gr []     uset = uset
        schedule' gr (e:es) uset = schedule' gr' (entries gr') uset' 
          where uset'       = uset ++ [e]
                (gr',_)     = deleteWithEntries e gr


-- auxiliary, for creating dependencies
allPairs :: [a] -> [(a,a)]
allPairs []       = []
allPairs (x:xs)   = bothDirs ++ allPairs xs
  where bothDirs  = concat [ [(x,t),(t,x)] | t <- xs ]

