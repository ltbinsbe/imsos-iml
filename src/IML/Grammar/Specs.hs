
module IML.Grammar.Specs where

import IML.Grammar.Shared
import IML.Grammar.High
import IML.Grammar.Low

import Funcons.Operations hiding (MVar)

import Data.Text (pack, unpack)

import qualified Data.Map as M

data Spec a     = Spec [AnyDecls a]
type HighSpec   = Spec Rule
type LowSpec    = Spec ProcDecl 

data AnyDecls a = AnEntDecl EntDecl
                | ATConsDecl TConsDecl
                | ARelDecl RelDecl
                | AVarDecl VarDecl
                | ARuleDecl a

-- of the possible sequences the variable can match, which to try first?
data EntDecl    = EntDecl EID [Expr]
data TConsDecl  = PCTerm RSymb (Either BuiltinType Cons)
                | EIDTerm EID (Either BuiltinType Cons)
data RelDecl    = RelDecl RSymb [RelPred]
data RelPred    = IsPure 
                | Orderable
                | Reflexive
                | Repeatable 
                | HasValueOps
                deriving (Enum, Ord, Eq)

instance Show RelPred where
  show Reflexive       = "REFLEXIVE"
  show IsPure          = "CONTEXT_FREE"
  show Orderable       = "ORDERABLE"
  show Repeatable      = "REPEATABLE"
  show HasValueOps     = "VALUE-OPERATIONS"

type ProcDecl    = AProcDecl [Stmts]
data AProcDecl t = Proc Int {- prio -} 
                          RSymb 
                          (Either Int [StaticPattern]) -- int indicates min seq-length
                          t 
data StaticPattern = TeCons Cons
                   | VaCons Cons
                   | TyCons Cons
                   | NoCons Int (Maybe Int)  -- min/max amount the pattern will match
                   deriving (Ord, Eq)

mkStaticPattern :: M.Map MVar VarDecl -> [Pattern] -> Either Int [StaticPattern]
mkStaticPattern vm ps 
  | any matchSeq statPat = Left (foldr count 0 statPat)
  | otherwise            = Right statPat
  where
    count (NoCons i _)  = (i+)
    count _             = (1+)
    matchSeq (NoCons i j) = not (i == 1 && j == Just 1)
    matchSeq _            = False
    statPat = map mCons ps
    mCons (PCons cs _)              = TeCons cs
    mCons (PVal (ADTVal cs _))      = VaCons $ unpack cs
    mCons (PVal (ComputationType (Type (ADT cs _))))  = TyCons $ unpack cs
    mCons (PVal _)                  = NoCons 1 $ Just 1
    mCons PAny                      = NoCons 1 $ Just 1
    mCons (PVar x)                  = case M.lookup x vm of
      Nothing                     -> NoCons 1 $ Just 1
      Just (VarDecl _ lb mub _ _) -> NoCons lb mub
    
mkVarMap :: [VarDecl] -> M.Map MVar VarDecl
mkVarMap vds = foldr op M.empty vds
  where op d@(VarDecl x _ _ _ _) = M.insert x d 

eidOfDecl :: EntDecl -> EID
eidOfDecl (EntDecl eid _) = eid

partition_decls :: [AnyDecls a] -> ([EntDecl], [TConsDecl], [RelDecl], [VarDecl], [a])
partition_decls = foldr op ([],[],[],[],[])
  where op (AnEntDecl x)  (xs,ys,zs,vs,as) = (x:xs,ys,zs,vs,as)
        op (ATConsDecl y) (xs,ys,zs,vs,as) = (xs,y:ys,zs,vs,as)
        op (ARelDecl z)   (xs,ys,zs,vs,as) = (xs,ys,z:zs,vs,as)
        op (AVarDecl v)   (xs,ys,zs,vs,as) = (xs,ys,zs,v:vs,as)
        op (ARuleDecl a)  (xs,ys,zs,vs,as) = (xs,ys,zs,vs,a:as)

withDecl :: (EntDecl -> a) -> (TConsDecl -> a) -> (RelDecl -> a) -> (VarDecl -> a) -> (b -> a) -> AnyDecls b -> a
withDecl f _ _ _ _ (AnEntDecl x)   = f x
withDecl _ f _ _ _ (ATConsDecl x)  = f x
withDecl _ _ f _ _ (ARelDecl x)    = f x
withDecl _ _ _ f _ (AVarDecl x)    = f x
withDecl _ _ _ _ f (ARuleDecl x)   = f x

relFromAnyDecls :: [AnyDecls a] -> RelTable
relFromAnyDecls decls = relFromDecls rels 
  where (_,_,rels,_,_) = partition_decls decls  

relFromDecls :: [RelDecl] -> RelTable
relFromDecls = foldr op relEmpty . zip [1..]
    where op (k, RelDecl r ps) = relInsert r k ps

instance Functor AnyDecls where
  fmap f (AnEntDecl x)  = AnEntDecl x
  fmap f (ARelDecl x)   = ARelDecl x
  fmap f (ATConsDecl x) = ATConsDecl x
  fmap f (AVarDecl x)   = AVarDecl x
  fmap f (ARuleDecl x)  = ARuleDecl (f x)

instance Foldable AnyDecls where
  foldMap f (AnEntDecl x)   = mempty 
  foldMap f (ARelDecl x)    = mempty
  foldMap f (ATConsDecl x)  = mempty
  foldMap f (AVarDecl x)    = mempty
  foldMap f (ARuleDecl x)   = f x

instance Traversable AnyDecls where
  traverse f (AnEntDecl x)    = pure (AnEntDecl x)
  traverse f (ARelDecl x)     = pure (ARelDecl x)
  traverse f (ATConsDecl x)   = pure (ATConsDecl x)
  traverse f (AVarDecl x)     = pure (AVarDecl x)
  traverse f (ARuleDecl x)    = ARuleDecl <$> f x

-- relation info
data RelInfo    = RelInfo { rel_id :: Int
                          , rel_preds :: [RelPred] 
                          }
type RelTable   = M.Map RSymb RelInfo 

relEmpty :: RelTable 
relEmpty = M.empty

relInsert :: RSymb -> Int -> [RelPred] -> RelTable -> RelTable
relInsert r k ps = M.insert r (RelInfo k ps)

instance Functor Spec where
  fmap f (Spec xs) = Spec $ fmap (fmap f) xs

instance Functor AProcDecl where
  fmap f (Proc i r c ss) = Proc i r c (f ss) 

instance Foldable Spec where
  foldMap f (Spec ds) = foldMap (foldMap f) ds

instance Foldable AProcDecl where
  foldMap f (Proc i r c ss) = f ss

instance Traversable Spec where
  traverse f (Spec ds) = 
    Spec <$> traverse (traverse f) ds

instance Traversable AProcDecl where
  sequenceA (Proc i r c ss) = Proc i r c <$> ss


