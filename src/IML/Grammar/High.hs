
module IML.Grammar.High (
  Rule(..), Conclusion(..), Premises, Premise(..), SideCons, SideCon(..), priorityOf,
  Term(..), Pattern(..), RoUp(..), EntUp(..), EntAcc(..), MVar(..),
  Cons, RSymb, Rep(..),Expr(..),VarDecl(..),VarStrat(..), 
  TConf(..), PConf(..),
  sRel, mRel,
  ) where

import IML.Grammar.Shared

data TConf      = TConf [Expr] [EntUp]
data PConf      = PConf [Pattern] [EntAcc]

type Premises   = [Premise]
data Premise    = Prem [RoUp] {- turnstile -} TConf RSymb PConf

data Conclusion = Concl [EntAcc] {- turnstile -} PConf RSymb TConf 

type SideCons   = [SideCon]
data SideCon    = SideOP [Expr] [Pattern]
                | Term ConsSetKey [Expr]
                | NonTerm ConsSetKey [Expr]

data VarDecl    = VarDecl MVar Int (Maybe Int) VarStrat [Either Premise SideCon]
data VarStrat   = Longest | Shortest | Random 

type Prio       = Int
data Rule       = Rule Prio Conclusion [Either Premise SideCon]
                                       [VarDecl]

priorityOf :: Rule -> Prio
priorityOf (Rule p _ _ _) = p

type EntAcc     = (EID, [Pattern])
type EntUp      = (EID, [Expr])
type RoUp       = (EID, [Expr]) 

