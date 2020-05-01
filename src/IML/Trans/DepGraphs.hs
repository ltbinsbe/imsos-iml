{-# LANGUAGE StandaloneDeriving #-}

module IML.Trans.DepGraphs where

import IML.Grammar
import IML.Trans.Graphs

data Branch       =   Branch  [Stmt] {- no branches or commits -}
                              (BranchEnd Branch)

data BranchEnd b  =   Br  [b]
                  |   Cmt Term

data DepGraph     = DepGraph (Graph Stmt) (BranchEnd DepGraph) -- graph and sink 

liftDGget :: (Graph Stmt -> b) -> DepGraph -> b
liftDGget f (DepGraph gr _) = f gr

liftDGset :: (Graph Stmt -> Graph Stmt) -> DepGraph -> DepGraph
liftDGset f (DepGraph gr end) = DepGraph (f gr) end


maxDepGraphDepth :: DepGraph -> Int
maxDepGraphDepth (DepGraph g end) = case end of
  Cmt t -> maxDepth g + 1
  Br gs -> maxDepth g + 1 + maximum (map maxDepGraphDepth gs)

depGraphNodes :: DepGraph -> Int
depGraphNodes (DepGraph g end) = case end of 
  Cmt t -> length (nodes g) + 1
  Br gs -> length (nodes g) + 1 + sum (map depGraphNodes gs)


