{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

module IML.Grammar.Shared where

import Prelude hiding (AnEntDecl, ARuleDecl)

import Funcons.Operations (HasValues(..), Values(..), vmap)

import Data.Either (lefts, rights)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Funcons.Operations as VOP

type RSymb      = String
type Cons       = String
type EID        = String
type VOP        = String
type MVar       = String

prebound_mvar :: MVar
prebound_mvar = "__T0"

user_priority :: Int
user_priority = 10

data BuiltinType= Booleans
                | Integers
                | Strings
                | Characters
                | Lists
                | Sets
                | Tuples
                | Types
                | ADTs
                | Atoms
                | Maps
                | Values 
                deriving (Eq, Ord)

data Rep        = NoRep | Rep
                deriving (Ord, Eq)

sRel r          = r
mRel r          = r ++ "*"

type Exprs      = [Expr]
data Expr       = ETerm Term {- value -}
                | VOP VOP Exprs

data Term       = TVar MVar
                | TVal (Values Term)
                | TCons Cons [Term]
                deriving (Eq, Ord)

instance Funcons.Operations.HasValues Term where
  project t = case t of TVal v  -> Just v
                        _       -> Nothing
  inject = TVal

data Pattern    = PCons Cons [Pattern]
                | PVar MVar
                | PAny
                | PVal (Values Pattern)
                deriving (Eq, Ord)

instance Funcons.Operations.HasValues Pattern where
  project t = case t of PVal v  -> Just v
                        _       -> Nothing
  inject = PVal

term2pattern :: Term -> Pattern
term2pattern (TVar v) = PVar v
term2pattern (TVal v) = PVal (Funcons.Operations.vmap term2pattern v)
term2pattern (TCons cs ts) = PCons cs (map term2pattern ts)

instance Show BuiltinType where
  show Booleans   = "BOOLEANS"
  show Atoms      = "ATOMS"
  show Values     = "VALUES"
  show Maps       = "MAPS"
  show Strings    = "STRINGS"
  show Integers   = "INTEGERS"
  show Characters = "CHARACTERS"
  show ADTs       = "ADTS"
  show Lists      = "LISTS"
  show Sets       = "SETS"
  show Tuples     = "TUPLES"
  show Types      = "TYPES"

type ConsSetKey = String {- RSymb or EID -}
type ConsSet    = M.Map ConsSetKey (S.Set (Either BuiltinType Cons))

isVal :: ConsSet -> ConsSetKey -> Term {- closed -} -> Bool
isVal css k t = case t of
  TVal _ | Values `S.member` types -> True
  TVal (VOP.ADTVal "true" _)  -> Booleans `S.member` types
                                  || ADTs `S.member` types
  TVal (VOP.ADTVal "false" _) -> Booleans `S.member` types
                                  || ADTs `S.member` types
  TVal v@(VOP.ADTVal "list" _)
    | VOP.isString_ v         -> Strings  `S.member` types
  TVal (VOP.ADTVal "list" _)  -> Lists `S.member` types
  TVal (VOP.ADTVal "tuple" _) -> Tuples `S.member` types
  TVal (VOP.ADTVal _ _)       -> ADTs `S.member` types
  TVal (VOP.Set s)  -> Sets `S.member` types
  TVal (VOP.Int _)            -> Integers `S.member` types
  TVal (VOP.Nat _)            -> Integers `S.member` types
  TVal v | Just c <- VOP.upcastCharacter v -> Characters `S.member` types
  TVal (VOP.ComputationType (VOP.Type _)) -> Types `S.member` types
  TVal (VOP.Atom _)           -> Atoms `S.member` types
  TVal (VOP.Map  _)           -> Maps `S.member` types
  TVal _                      -> False
  TVar _                      -> error "isVal variable"
  TCons cs _                  -> cs `S.member` conss
  where types = maybe S.empty (S.fromList . lefts . S.toList) entries
        conss = maybe S.empty (S.fromList . rights . S.toList) entries
        entries = M.lookup k css

isGroundVal :: ConsSet -> RSymb -> Term -> Bool
isGroundVal css k t@(TVal v) = isVal css k t
isGroundVal css k (TVar _) = error "isGroundVal variable"
isGroundVal css k t@(TCons cs ts) = isVal css k t && all (isGroundVal css k) ts

isTVar :: Term -> Bool
isTVar (TVar _) = True
isTVar _ = False

isPVar :: Pattern -> Bool
isPVar (PVar _) = True
isPVar _ = False

unPVar :: Pattern -> MVar
unPVar (PVar var) = var
unPVar _ = error "unPVar"

isTerm :: Expr -> Bool
isTerm (ETerm _) = True
isTerm _ = False

unTerm :: Expr -> Term
unTerm (ETerm t) = t
unTerm _ = error "unTerm"
