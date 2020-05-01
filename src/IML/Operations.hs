{-# LANGUAGE OverloadedStrings #-}

module IML.Operations where

import IML.Grammar.Shared
import Funcons.Operations 
import qualified Funcons.Operations as VAL

import Data.String
import Data.Text (pack,unpack)

library = VAL.libUnite $ VAL.library:[VAL.libFromList [
    ("term-constructor", UnaryExpr term_constructor)
  , ("term-arguments", UnaryExpr term_arguments)
  , ("term-construct", NaryExpr term_construct_)
  ]]

term_constructor_ :: [OpExpr Term] -> OpExpr Term
term_constructor_ = unaryOp term_constructor
term_constructor  :: OpExpr Term -> OpExpr Term
term_constructor  = UnaryOp "term-constructor" op
  where op (TCons t _) = Normal $ inject $ fromString t
        op _           = SortErr "term-constructor not applied to a (closed) term"

term_arguments_ :: [OpExpr Term] -> OpExpr Term
term_arguments_ = unaryOp term_arguments
term_arguments  :: OpExpr Term -> OpExpr Term
term_arguments  = UnaryOp "term-arguments" op
  where op (TCons _ ts) = Normal (inject (multi ts))
        op _            = SortErr "term-arguments not applied to a (closed) term"

term_construct_ :: [OpExpr Term] -> OpExpr Term
term_construct_ = NaryOp "term-construct" op
  where op (TVal v:ts) | VAL.isString_ v = Normal (TCons (unString v) ts)
        op _ = SortErr "term-construct not applied to a string and a sequence of argument terms"


