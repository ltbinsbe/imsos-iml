{-# LANGUAGE FlexibleInstances, StandaloneDeriving #-}

module IML.Grammar.Bindings where

import IML.Grammar
import IML.Trans.ProMan
import Funcons.Operations(Values(ADTVal,ComputationType),ComputationTypes(Type),Types(ADT))

import Data.Maybe (isJust, fromJust)
import qualified Data.Map as M
import qualified Data.Set as S

type SubsPair = (SubsEnv, SubsEnv) 
type UnificationRes = ProMan (Maybe (SubsEnv, SubsEnv))

type SubsEnv = M.Map MVar MVar

replaces :: SubsEnv -> MVar -> Bool
replaces = (maybe False (const True) .) . flip M.lookup 

replace :: SubsEnv -> MVar -> MVar
replace = (maybe (error "replace") id .) . flip M.lookup

-- | Replace the meta-variable by its binding in the given 
-- substitution environment. 
-- Only performs a single replacement (or none at all). 
mreplace :: SubsEnv -> MVar -> MVar
mreplace the x = maybe x id $ M.lookup x the

-- | 'v1 `rep` v2' creates a singleton meta-environment
-- in which v1 is bound to v2
rep :: MVar -> MVar -> SubsEnv
rep = M.singleton

subsInsert :: MVar -> MVar -> SubsEnv -> SubsEnv
subsInsert = M.insert 

subsEnvFromList :: [(MVar,MVar)] -> SubsEnv
subsEnvFromList = M.fromList

subsEmpty :: SubsEnv
subsEmpty = M.empty

subsUnion :: SubsEnv -> SubsEnv -> SubsEnv
subsUnion = M.unionWithKey op
  where op k = error ("meta-variable " ++ show k ++ " occurs in multiple patterns")

subsPairsUnion :: [SubsPair] -> (SubsEnv, SubsEnv)
subsPairsUnion = foldr subsPairUnion (subsEmpty, subsEmpty)

subsPairUnion :: SubsPair -> SubsPair -> (SubsEnv, SubsEnv)
subsPairUnion (the1, the2) (the11, the22) = 
  (the1 `subsUnion` the11, the2 `subsUnion` the22)

-- | Compute the inverse of a substitution environment
subsInverse :: SubsEnv -> SubsEnv
subsInverse = M.foldrWithKey op M.empty
  where op f t m = M.insert t f m

-- | Compute a substitution environment by `merging' two substitution
-- environments based on transitivity. That is:
-- if a |-> b  and b |-> c then in the new map a |-> c
-- if no such see then just a |-> b
subsTrans :: SubsEnv -> SubsEnv -> SubsEnv
subsTrans m1 m2 = M.foldrWithKey op M.empty m1
  where op f t m3 = case M.lookup t m2 of
                      Nothing   -> M.insert f t m3
                      Just t'   -> M.insert f t' m3

-- | Left-biased unification operator. 
-- It is left-biased in that the second operand is compared against
-- the first operand. If the two are unifiable, proof is returned
-- in the form a substitution that suggests replacements on the second operand.
unify_with_bias :: HasMVar a => a -> a -> ProMan (Maybe SubsEnv)
unify_with_bias a1 a2 = fmap merge <$> unify a1 a2
  where merge (th1,th2) = subsTrans th2 (subsInverse th1) 

un_success :: UnificationRes
un_success = return (return (subsEmpty,subsEmpty))

un_failure :: UnificationRes
un_failure = return Nothing

un_and :: UnificationRes -> UnificationRes -> UnificationRes
un_and m1 m2 = (\mres1 mres2 -> subsPairUnion <$> mres1 <*> mres2) <$> m1 <*> m2

-- | Class of types that contain meta-variables
class HasMVar a where
  -- | Replace any occurring meta-variables bound in the given |SubsEnv|
  --  by the meta-variable to which they are bound
  sub_mvars :: SubsEnv -> a -> a

  -- | Perform unification on two values, subject to a substitution-environment,
  -- resulting in:
  --  * two substitution-environments, one for each operand
  --  * failure (Nothing)
  -- may involve the generation of fresh meta-variables
  unify_within :: SubsPair -> a -> a -> UnificationRes 

  -- | Basic unification without `context`
  unify :: a -> a -> UnificationRes 
  unify = unify_within (subsEmpty, subsEmpty)

unify_pvar :: MVar -> MVar -> UnificationRes
unify_pvar x1 x2 
  |  x1 == x2 = un_success
  | otherwise = case (x1,x2) of
      {-(MVar _ l1 ml1, MVar _ l2 ml2) | l1 == l2, ml1 == ml2  
          -> do   nm <- fresh_var_name
                  let x = MVar nm l1 ml2
                  return (Just (rep x1 x, rep x2 x))-}
      _   -> do   x3 <- fresh_var_name
                  return (Just (rep x1 x3, rep x2 x3) )

unify_pvars :: [MVar] -> [MVar] -> UnificationRes
unify_pvars xs ys 
    | length xs == length ys = do
        msenvs <- sequence (zipWith unify_pvar xs ys)
        case all isJust msenvs of
          True  -> return $ Just (subsPairsUnion (map fromJust msenvs))
          False -> return Nothing
    | otherwise = return Nothing

instance HasMVar a => HasMVar [a] where
  sub_mvars the = map (sub_mvars the)

  unify_within thep xs ys 
    | length xs == length ys = do
        msenvs <- sequence (zipWith (unify_within thep) xs ys)
        case all isJust msenvs of
          True  -> return $ Just (subsPairsUnion (map fromJust msenvs))
          False -> return Nothing
    | otherwise = return Nothing

-- | Class of types that have meta-variables in `binding positions'
class HasPVar a where
  -- | Return the meta-variables in bindings positions as a set
  pvars :: a -> [MVar]
  
  pvars_set :: a -> S.Set MVar
  pvars_set = S.fromList . pvars

instance HasPVar a => HasPVar [a] where
  pvars = concatMap pvars

-- Class of types that have meta-variables in `term positions'
class HasTVar a where
  -- | Return the meta-variables in "term positions"
  tvars  :: a -> [MVar]

  tvars_set :: a -> S.Set MVar
  tvars_set = S.fromList . tvars

instance HasTVar a => HasTVar [a] where
  tvars = concatMap tvars

instance (HasMVar a, HasMVar b) => HasMVar (Either a b) where
  sub_mvars the (Left a) = Left (sub_mvars the a)
  sub_mvars the (Right b) = Right (sub_mvars the b)
  unify_within the s1 s2 = case (s1,s2) of
    (Left a, Left b)    -> unify_within the a b
    (Right a, Right b)  -> unify_within the a b 
    _                   -> un_failure

-- HasMVar instances
instance HasMVar Stmt where 
  sub_mvars the s = case s of 
    Commit t si         -> Commit (sub_mvars the t) si
    Trans  r t x ml     -> Trans r (sub_mvars the t) (map (mreplace the) x) ml
    PM e p              -> PM (sub_mvars the e) (sub_mvars the p)
    Set eid e l         -> Set eid (sub_mvars the e) l
    Get eid x l         -> Get eid (map (mreplace the) x) l
    Branches sss        -> Branches (sub_mvars the sss)
    IsTerm r t          -> IsTerm r (sub_mvars the t)
    IsNonTerm r t       -> IsNonTerm r (sub_mvars the t)

  unify_within the s1 s2 = case (s1, s2) of
    (Commit t1 _, Commit t2 _) -> unify_within the t1 t2
    (Trans  r1 t1 x1 ml1, Trans r2 t2 x2 ml2) -> unifyCall r1 t1 x1 ml1 r2 t2 x2 ml2
    (PM e1 p1, PM e2 p2)  -> unify_within the e1 e2 `un_and` unify_within the p1 p2
    (Set eid1 e1 l1, Set eid2 e2 l2) | eid1 == eid2, l1 == l2 -> unify_within the e1 e2
    (Get eid1 x1 l1, Get eid2 x2 l2) | eid1 == eid2, l1 == l2 -> unify_pvars x1 x2
    (Branches _, _) -> error "unification on branches?"
    (_, Branches _) -> error "unification on branches?"
    (_,_) -> un_failure 
   where
      unifyCall r1 t1 x1 ml1 r2 t2 x2 ml2 =
        if r1 == r2 && ml1 == ml2 
        then unify_within the t1 t2 `un_and` unify_pvars x1 x2
        else un_failure

instance HasMVar Expr where
  sub_mvars the (ETerm t)      = ETerm (sub_mvars the t) 
  sub_mvars the (VOP op es)  = VOP op (sub_mvars the es) 

  unify_within the e1 e2 = case (e1, e2) of 
    (ETerm v1, ETerm v2) -> unify_within the v1 v2 
    (VOP o1 es1, VOP o2 es2) | o1 == o2 -> unify_within the es1 es2 
    (_,_) -> return Nothing

instance HasMVar Term where
  sub_mvars the (TVar x)     = TVar (mreplace the x) 
  sub_mvars the (TVal v)     = TVal v
  sub_mvars the (TCons f ts) = TCons f (sub_mvars the ts)

  unify_within thep@(the1,the2) t1 t2 = case (t1, t2) of 
    (TVar x1, TVar x2) | x1' == x2' -> un_success
      where x1' = mreplace the1 x1
            x2' = mreplace the2 x2
    (TCons f1 ts1, TCons f2 ts2) | f1 == f2-> 
      unify_within thep ts1 ts2
    (_,_) -> return Nothing

instance HasMVar Pattern where
  sub_mvars the p = case p of
    PAny          -> PAny
    PVal vp       -> PVal vp 
    PVar x        -> PVar (mreplace the x)
    PCons cs ps   -> PCons cs (sub_mvars the ps)

  unify_within the p1 p2 = case (p1,p2) of
    (PVar x1, PVar x2)        -> unify_pvar x1 x2
    (PAny, PAny)              -> un_success
    (PVal v1, PVal v2) 
      | v1 == v2              -> un_success 
    (PCons cs1 ps1, PCons cs2 ps2)
      | cs1 == cs2            -> unify_within the ps1 ps2
    (_, _)                    -> return Nothing

{-
instance HasMVar (VPattern Term) where
  sub_mvars the (VPMVar x)     = VPMVar (mreplace the x) 
  sub_mvars the (VPLit v)     = VPLit v
  sub_mvars the VPAny         = VPAny
  sub_mvars the (VPADT f ts) = VPADT f (sub_mvars the ts)
  sub_mvars the (VPThunk b)   = VPThunk $ sub_mvars the b

  unify_within the p1 p2 = case (p1,p2) of
    (VPMVar x1, VPMVar x2)  -> unify_pvar x1 x2
    (VPAny, VPAny)        -> un_success
    (VPADT f1 ps1, VPADT f2 ps2) | f1 == f2 -> unify_within the ps1 ps2
    (_, _) -> return Nothing
-}

instance (HasTVar a, HasTVar b) => HasTVar (Either a b) where
  tvars = either tvars tvars

-- HasTVar instances
instance HasTVar Stmt where
  tvars s = case s of
    Trans  _ t _ _      -> tvars t
    PM e _              -> tvars e
    Set _ e _         -> tvars e
    Get _ _ _        -> [] 
    -- should not be executed
    Commit t _          -> tvars t
    Branches sss        -> tvars sss
    IsTerm r t          -> tvars t 
    IsNonTerm r t       -> tvars t 

instance HasTVar Expr where
  tvars e = case e of 
    ETerm t               -> tvars t
    VOP _ es            -> concatMap tvars es

instance HasTVar Term where
  tvars t = case t of
    TVar x              -> (:[]) x
    TVal (ADTVal _ ts)  -> concatMap tvars ts
    TVal (ComputationType (Type (ADT _ ts))) -> concatMap tvars ts
    TVal v              -> []
    TCons _ ts          -> concatMap tvars ts

instance HasTVar SideCon where
  tvars sc = case sc of 
    SideOP exprs pats -> tvars exprs
    Term _ exprs      -> tvars exprs   
    NonTerm _ exprs   -> tvars exprs

instance HasTVar Premise where
  tvars (Prem ros tconf _ _) = tvars (concatMap snd ros) ++ tvars tconf 

instance HasTVar TConf where
  tvars (TConf exprs ups) = tvars exprs ++ tvars (concatMap snd ups) 

-- HasPVar instances 
instance (HasPVar a, HasPVar b) => HasPVar (Either a b) where
  pvars = either pvars pvars

instance HasPVar Stmt where
  pvars s = case s of 
    Commit _ _          -> []
    Trans  _ _ xs _     -> xs
    PM _ p              -> pvars p
    Get _ _ _        -> []
    Set _ _ _        -> []
    -- should not be executed
    Branches sss        -> pvars sss
    IsTerm _ _          -> []
    IsNonTerm _ _       -> [] 

instance HasPVar Pattern where 
  pvars p = case p of 
    PAny                -> []
    PVal (ADTVal _ ps)  -> pvars ps
    PVal (ComputationType (Type (ADT _ ps))) -> pvars ps
    PVal vp             -> [] 
    PVar x              -> [x] 
    PCons _ ps          -> pvars ps

instance HasPVar SideCon where
  pvars sc = case sc of 
    SideOP _ pats -> pvars pats
    Term _ _      -> []
    NonTerm _ _   -> []

instance HasPVar Premise where
  pvars (Prem _ _ _ pconf) = pvars pconf

instance HasPVar PConf where
  pvars (PConf pats downs) = pvars pats ++ pvars (concatMap snd downs)

{-
instance HasPVar (VPattern Term) where
  pvars p = case p of
    VPMVar x              -> (:[]) x
    VPLit _               -> []
    VPAny                 -> []
    VPADT _ ps            -> concatMap pvars ps
    VPThunk b             -> [] 
-}

get_eidss :: Stmts -> S.Set EID
get_eidss = S.unions . map get_eids

get_eids :: Stmt -> S.Set EID
get_eids s = case s of 
  Branches sss  -> S.unions $ concatMap (map get_eids) sss
  Set eid _ _   -> S.singleton eid
  Get eid _ _   -> S.singleton eid
  _             -> S.empty
