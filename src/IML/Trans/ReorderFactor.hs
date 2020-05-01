
module IML.Trans.ReorderFactor where

import IML.Grammar
import IML.Grammar.Bindings

import IML.Trans.Graphs
import IML.Trans.ProMan

import Data.Maybe (catMaybes)
import Data.List (minimumBy, partition)
import Data.Foldable (foldrM)

type ISect = [(Stmt, [Graph Stmt])]
type CSet  = [(Stmt, Graph Stmt)]

reorder_factor :: Traversable f => Component (f [Graph Stmt]) (f [Stmts])
reorder_factor = component (traverse schedule)

schedule :: [Graph Stmt] -> ProMan [Stmts]
schedule gs = widen <$> lzip gs 
 where widen sched = case sched of  [Branches bs] -> bs 
                                    _             -> [sched]

lzip :: [Graph Stmt] -> ProMan Stmts 
lzip gs
  | null gs       = error "lzipping empty set of dependency graphs" 
  | null nonempts = return []
  | otherwise     = do  
          let csets = map to_cset nonempts
                where -- to_cset :: Graph a -> CSet a 
                      to_cset gr = zip (entries gr) (repeat gr)
          iss <- select csets 
          case iss of
            []    -> error "select returns no sequence of intersections"
            [is]  -> withSingleI is
            _     -> (:[]) . Branches <$> mapM withSingleI iss
  where 
        (empts,nonempts) = partition nullNodes gs
        withSingleI :: ISect -> ProMan Stmts 
        withSingleI is = case is of
              []          -> error "select returns empty intersection"
              -- TODO does it matter which 'a' to choose?
              ((a,conts):_)  -> (a:) <$> lzip conts

select :: [CSet] -> ProMan [ISect]
select css = do
  -- consider each possible order between choicesets
  isss <- mapM intersects (permutations css)  
  -- return only the "best" list of intersections (hopefully just 1 complete intersection)
  return (minimumBy selector isss)
  where -- TODO what if there equal solutions w.r.t. to this selector?
        -- more than 1 complete intersection
        -- or more than 1 incomplete intersections (length > 1)
        selector :: [ISect] -> [ISect] -> Ordering
        selector xs ys = length xs `compare` length ys

        permutations = (:[])

-- | Compute a sequence of intersections between a list of choice sets
-- a new intersection is started whenever an empty intersection 
-- would have been encountered
intersects :: [CSet] -> ProMan [ISect]
intersects css = do   
  (mis, iss) <- foldrM op (Nothing, []) css
  case mis of
    Nothing -> error "no choice sets given?"
    Just is -> return (is:iss)              
  where
    op :: CSet -> (Maybe ISect, [ISect]) -> ProMan (Maybe ISect, [ISect])
    op [] _               = error "empty choice set?"
    op cs (Nothing, [])   = return (Just (cset2isect cs), [])
    op cs (Nothing, _)    = error "intersects, intermediate Nothing"
    op cs (Just is, iss)  = do
      is' <- intersect cs is  
      case is' of
        []  -> return (Just (cset2isect cs), is:iss)
        _   -> return (Just is', iss)

    cset2isect :: CSet -> ISect
    cset2isect = fmap op
      where op (a, dg) = (a, [dg'])
              where dg' = delete a dg 

-- | Compute the intersection between a choice set and an intersection
intersect :: CSet -> ISect -> ProMan ISect
intersect cs is = catMaybes <$> sequence 
  -- TODO, this computation may include too many elements
  -- namely when an element may be unified with more than 1 
  -- element in the current intersection 
  [ attempt a1 g1 a2 gs | (a1, g1) <- cs, (a2, gs) <- is ]
 where
  attempt :: Stmt -> Graph Stmt -> Stmt -> [Graph Stmt] -> ProMan (Maybe (Stmt, [Graph Stmt]))
  attempt a1 g1 a2 gs = do
    ma_ <- unify a1 a2 
    case ma_ of 
      Nothing           -> return Nothing
      Just (th1,th2)    -> 
        let g1'   = graphMap (sub_mvars th1) (delete a1 g1)
            gs'   = map (graphMap (sub_mvars th2)) gs 
        in return $ Just (sub_mvars th1 a1, g1' : gs')
