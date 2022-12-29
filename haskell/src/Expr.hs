{-# LANGUAGE ScopedTypeVariables #-}

module Expr where

import Data.SBV

data IExpr =
  Const Int8        |
  Var String        |
  Plus IExpr IExpr  |
  Minus IExpr IExpr |
  Mod IExpr IExpr   |
  Ite BExpr IExpr IExpr
  deriving Show

data BExpr =
  BFalse            |
  BTrue             |
  BAnd BExpr BExpr  |
  BOr BExpr BExpr   |
  BNot BExpr        |
  BEq IExpr IExpr   |
  BNeq IExpr IExpr  |
  BLt IExpr IExpr   |
  BLe IExpr IExpr   |
  BGt IExpr IExpr   |
  BGe IExpr IExpr
  deriving Show
