{-# OPTIONS --erased-cubical --safe #-}

module Expr where

open import Prelude hiding (#_; _==_) renaming ( _∨_ to _∨b_; _∧_ to _∧b_)

open import Util using (_==ℤ_; _<ℤ_; _≤ℤ_)

infix 10 #_
infixr 9 ¬_
infixr 6 _∧_
infixr 5 _∨_
infix  4 _==_

data IExpr : Type where
  #_ : ℤ → IExpr
  var   : String → IExpr

data BExpr : Type where
  false : BExpr
  true  : BExpr
  _==_  : IExpr → IExpr → BExpr
  _<_   : IExpr → IExpr → BExpr
  _≤_   : IExpr → IExpr → BExpr
  _∨_   : BExpr → BExpr → BExpr
  _∧_   : BExpr → BExpr → BExpr
  ¬_    : BExpr → BExpr

-- For now variables are evaluated to -1
evalI : IExpr → ℤ
evalI (#   n) = n
evalI (var _) = -[1+ 0 ]

evalB : BExpr → Bool
evalB false    = false
evalB true     = true
evalB (x == y) = evalI x ==ℤ evalI y
evalB (x < y)  = evalI x <ℤ evalI y
evalB (x ≤ y)  = evalI x ≤ℤ evalI y
evalB (x ∨ y)  = evalB x ∨b evalB y
evalB (x ∧ y)  = evalB x ∧b evalB y
evalB (¬ x)    = not (evalB x)

all : List BExpr → BExpr
all = foldr _∧_ true
