{-# LANGUAGE FlexibleInstances, StandaloneDeriving #-}

module IML.Grammar.Low where

import IML.Grammar.Shared hiding (Spec(..))

type Stmts      = [Stmt]
data Stmt       = Branches    [Stmts]
                | PM          [Expr]      [Pattern]
                | IsTerm      ConsSetKey  [Term]
                | IsNonTerm   ConsSetKey  [Term]
                | Trans       RSymb       [Term]  [MVar] Label
                | Commit      [Term]      (Maybe StaticRuleInfo)
                | Get         EID         [MVar]         Label
                | Set         EID         [Term]         Label

type Label      = Int

-- The purpose of `StaticRuleInfo` is to provide certain static information
-- about the context of a particular occurrence of `Commit`, without
-- changing its semantics
data StaticRuleInfo = SRI { rule_id :: Int
                          , ent_ids :: [EID] }
  deriving (Eq, Ord)

expectedCostOf :: Stmt -> Float 
expectedCostOf s = (expectedSuccessRateOf s *) $ case s of
  PM _ _                  -> low
  Trans _ _ _ _           -> medium + dev
  Get _ _ _               -> low 
  Set _ _ _               -> low + dev
  _                       -> medium
  where high    = 100
        low     = dev
        none    = 0
        medium  = 50
        dev     = 10

expectedSuccessRateOf :: Stmt -> Float
expectedSuccessRateOf s = case s of
  PM _ _                  -> low
  Trans _ _ _ _           -> medium
  Get _ _ _               -> succeeds
  _                       -> medium
  where medium    = 0.5
        low       = fails + dev
        high      = succeeds - dev
        dev       = 0.2
        succeeds  = 1
        fails     = 0

labelOf :: Stmt -> Maybe Label 
labelOf (Get _ _ l)       = Just l
labelOf (Set _ _ l)       = Just l
labelOf (Trans _ _ _ l)   = Just l
labelOf _                 = Nothing

-- | Returns whether the statement performs a procedure call
isCaller :: Stmt -> Bool
isCaller (Trans _ _ _ _)    = True
isCaller _                  = False

deriving instance Ord Stmt 
deriving instance Eq Stmt
deriving instance Ord Expr
deriving instance Eq Expr
