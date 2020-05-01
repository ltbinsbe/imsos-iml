{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module IML.EDSL where

import qualified IML.Grammar.High (sRel, mRel)
import IML.Grammar hiding (sRel, mRel)
import IML.Grammar.Specs
import IML.Grammar.Bindings
import IML.Trans.Graphs
import qualified Funcons.Operations as VOP

import Data.List (intersect)

import Control.Monad.State

type RuleBuilder a = State Conf a

data Conf = Conf  { lhs_  :: Maybe PConf
                  , rhs_  :: [EntUp]
                  , conds :: [Either Premise SideCon]
                  , decls :: [AnyDecls Rule]
                  , vars  :: [VarDecl]
                  , seed  :: Int
                  }

evalRuleBuilder :: RuleBuilder a -> a
evalRuleBuilder b = evalState b defaultConf

execRuleBuilder :: RuleBuilder a -> HighSpec
execRuleBuilder b = Spec $ reverse $ decls $ execState b defaultConf

defaultConf :: Conf
defaultConf = (Conf Nothing [] [] [] [] 1)

fresh_var :: RuleBuilder MVar
fresh_var = do 
  i <- gets seed 
  modify (\conf -> conf { seed = i + 1 })
  return ("_Y" ++ show i)

lhs :: IsPatterns pats => pats -> RuleBuilder ()
lhs pat = do 
  conf <- get
  put $ conf { lhs_ = (Just (PConf (toPatterns pat) [])) }

acc :: IsPatterns pats => EID -> pats -> RuleBuilder ()
acc eid p = do 
  conf <- get
  case lhs_ conf of
    Nothing             -> return ()
    Just (PConf pat ps) -> put conf{ lhs_ = Just (PConf pat ((eid,toPatterns p):ps)) }

up :: IsExprs exprs => EID -> exprs -> RuleBuilder ()
up eid ex = do
  conf <- get
  put conf { rhs_ = ((eid,toExprs ex):rhs_ conf) }

pm :: (IsExprs exprs, IsPatterns pats) => exprs -> pats -> RuleBuilder ()
pm e p = cond (Right $ SideOP (toExprs e) (toPatterns p))

is_terminal = is_terminating
is_terminating,is_terminal :: IsExprs exprs => RSymb -> exprs -> RuleBuilder ()
is_terminating r c = cond (Right $ Term r (toExprs c))

is_non_terminal = is_non_terminating
is_non_terminating,is_non_terminal :: IsExprs exprs => RSymb -> exprs -> RuleBuilder()
is_non_terminating r c = cond (Right $ NonTerm r (toExprs c))

cond :: Either Premise SideCon -> RuleBuilder()
cond cd = do
  conf <- get
  put (conf {conds = cd:conds conf})

premise :: (IsTConf tconf, IsPConf pconf) => 
              tconf -> RSymb -> pconf -> RuleBuilder ()
premise lhs arr rhs = cond (Left (Prem [] (toTConf lhs) arr (toPConf rhs)))

sRel,mRel :: RSymb -> RSymb 
sRel = IML.Grammar.High.sRel
mRel = IML.Grammar.High.mRel

commit :: IsExprs exprs => RSymb -> exprs -> RuleBuilder ()
commit = commit_prio user_priority

commit_prio :: IsExprs exprs => Int -> RSymb -> exprs -> RuleBuilder ()
commit_prio prio rsymb term = do 
  conf <- get
  case lhs_ conf of  
    Nothing     -> error "commit without init (lhs)"
    Just pconf  -> put $ conf { lhs_ = Nothing
                              , decls = ARuleDecl rule:decls conf
                              , vars = [] 
                              , rhs_ = []
                              , conds = []
                              , seed = 1}
      where rule = Rule prio (Concl [] pconf rsymb
                     (TConf (toExprs term) (rhs_ conf)))
                        (order_by_dependencies (reverse (conds conf))) (vars conf)

add_decl_ :: AnyDecls Rule -> RuleBuilder ()
add_decl_ decl = do 
  conf <- get
  put conf{ decls = decl : decls conf }

add_var_decl_ :: VarDecl -> RuleBuilder ()
add_var_decl_ decl = do 
  conf <- get
  put conf{ vars = decl : vars conf }

ent_decl :: (IsExprs exprs) => EID -> exprs -> RuleBuilder()
ent_decl e ex = add_decl_ (AnEntDecl (EntDecl e (toExprs ex)))

term_pc :: RSymb -> (Either BuiltinType Cons) -> RuleBuilder ()
term_pc r ebc = add_decl_ (ATConsDecl (PCTerm r ebc))

term_eid :: EID -> (Either BuiltinType Cons) -> RuleBuilder ()
term_eid eid ebc = add_decl_ (ATConsDecl (EIDTerm eid ebc))

rel_decl :: RSymb -> [RelPred] -> RuleBuilder()
rel_decl r flags = add_decl_ (ARelDecl (RelDecl r flags))

var_decl :: MVar -> Int -> Maybe Int -> VarStrat -> [Either Premise SideCon] -> RuleBuilder () 
var_decl x lb mub strat conds = add_var_decl_ (VarDecl x lb mub strat conds)

vop :: IsExpr expr => VOP -> [expr] -> Expr
vop op = VOP op . map toExpr

vop_null :: VOP -> Expr
vop_null op = VOP op []

build_cong_rules = build_cong_rules_prem premise
build_cong_rules_prem :: (Term -> RSymb -> Pattern -> RuleBuilder())
  -> Int {- arity -} -> Cons -> RSymb -> RuleBuilder ()
build_cong_rules_prem mkPrem n cs rsymb = 
  mapM_ mkCong [1..n] 
  where mkCond vars i j | i == j    = mkPrem (TVar var) rsymb (PVar var')
                        | otherwise = return () 
          where var,var' :: MVar
                var   = vars !! (j-1)
                var'  = var ++ "'"
        mkCong i = do
          vars <- mapM (const fresh_var) [1..n] 
          lhs (PCons cs (map PVar vars))
          mapM_ (mkCond vars i) [1..n]
          commit rsymb (TCons cs (map (mkRHS vars) [1..n]))
          where mkRHS vars j    | i == j    = TVar (vars !! (j-1) ++ "'")
                                | otherwise = TVar (vars !! (j-1))

adt :: VOP.Name -> [t] -> VOP.Values t
adt = VOP.ADTVal

adt_type :: VOP.Name -> [t] -> VOP.Values t
adt_type = ((VOP.ComputationType .) VOP.Type .) . VOP.ADT

order_by_dependencies :: [Either Premise SideCon] -> [Either Premise SideCon]
order_by_dependencies conds = schedule (inserts es (initialise conds)) 
        -- `a < b` if `a` has a pattern variable which occurs as a term variable in `b`
  where es = filter (uncurry isDep) (allPairs conds)
                  where isDep a b = not (null (intersect (pvars a) (tvars b)))

{-
class IsTerm a where
  toTerm :: a -> Term
instance IsTerm (VOP.Values Term) where
  toTerm = TVal
instance IsTerm (VOP.Types Term) where
  toTerm = TVal . VOP.Type
instance IsTerm MVar where
  toTerm = TVar 
instance IsTerm Term where
  toTerm = id
-}

class IsPattern a where
  toPattern :: a -> Pattern
instance IsPattern (VOP.Values Pattern) where
  toPattern = PVal
instance IsPattern (VOP.Types Pattern) where
  toPattern = PVal . VOP.ComputationType . VOP.Type
instance IsPattern MVar where
  toPattern = PVar
instance IsPattern Pattern where
  toPattern = id
instance IsPattern Term where
  toPattern t = case t of 
    TVar var    -> PVar var
    TVal val    -> PVal $ VOP.vmap toPattern val
    TCons cs ts -> PCons cs (map toPattern ts)
class IsPatterns a where
  toPatterns :: a -> [Pattern]
instance IsPattern a => IsPatterns [a] where
  toPatterns = map toPattern
instance IsPatterns Pattern where
  toPatterns = (:[])
instance IsPatterns Term where
  toPatterns = toPatterns . toPattern
instance IsPatterns MVar where
  toPatterns = toPatterns . toPattern
instance IsPatterns (VOP.Types Pattern) where
  toPatterns = toPatterns . toPattern
instance IsPatterns (VOP.Values Pattern) where
  toPatterns = toPatterns . toPattern

class IsExpr a where
  toExpr :: a -> Expr
instance IsExpr Expr where
  toExpr = id
instance IsExpr Term where
  toExpr = ETerm
instance IsExpr (VOP.Values Term) where
  toExpr = toExpr . TVal 
instance IsExpr (VOP.ComputationTypes Term) where
  toExpr = toExpr . VOP.ComputationType
instance IsExpr (VOP.Types Term) where
  toExpr = toExpr . VOP.Type
class IsExprs a where
  toExprs :: a -> [Expr]
instance IsExpr a => IsExprs [a] where
  toExprs = map toExpr
instance IsExprs Term where
  toExprs = (:[]) . toExpr
instance IsExprs (VOP.Values Term) where
  toExprs = (:[]) . toExpr
instance IsExprs (VOP.ComputationTypes Term) where
  toExprs = (:[]) . toExpr
instance IsExprs (VOP.Types Term) where
  toExprs = (:[]) . toExpr
instance IsExprs Expr where
  toExprs = (:[])

class IsPConf a where
  toPConf :: a -> PConf
instance IsPConf PConf where
  toPConf = id
instance IsPConf [Pattern] where
  toPConf = flip PConf []
instance IsPConf Pattern where  
  toPConf = toPConf . (:[])

class IsTConf a where
  toTConf :: a -> TConf
instance IsTConf TConf where
  toTConf = id
instance IsTConf [Expr] where
  toTConf = flip TConf []
instance IsTConf [Term] where
  toTConf = flip TConf [] . map ETerm 
instance IsTConf Expr where
  toTConf = toTConf . (:[])
instance IsTConf Term where
  toTConf = toTConf . (:[])

deriving instance Eq SideCon
deriving instance Ord SideCon
deriving instance Eq Premise 
deriving instance Ord Premise
deriving instance Eq TConf 
deriving instance Ord TConf
deriving instance Eq PConf 
deriving instance Ord PConf
