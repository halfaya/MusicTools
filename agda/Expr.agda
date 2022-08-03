{-# OPTIONS --erased-cubical --safe #-}

module Expr where

open import Prelude hiding (#_; _==_; _+_; _mod_)
                    renaming ( _∨_ to _∨b_; _∧_ to _∧b_; _-_ to _-ℤ_; if_then_else_ to i_t_e_)

open import Util using (_==ℤ_; _≠ℤ_; _<ℤ_; _≤ℤ_; _modℤ_)

infix 10 #_
infixr 9 ¬_
infixl 9 _%_ _mod_
infixl 8 _+_ _-_
infix  7 _==_ _≠_ _<_ _≤_
infixr 6 _∧_
infixr 5 _∨_

data BExpr : Type
evalB : BExpr → Bool

data IExpr : Type where
  #_            : ℤ → IExpr
  var           : String → IExpr
  _+_           : IExpr → IExpr → IExpr
  _-_           : IExpr → IExpr → IExpr
  _%_           : IExpr → IExpr → IExpr
  if_then_else_ : BExpr → IExpr → IExpr → IExpr

data BExpr where
  false : BExpr
  true  : BExpr
  _==_  : IExpr → IExpr → BExpr
  _≠_   : IExpr → IExpr → BExpr
  _<_   : IExpr → IExpr → BExpr
  _≤_   : IExpr → IExpr → BExpr
  _∧_   : BExpr → BExpr → BExpr
  _∨_   : BExpr → BExpr → BExpr
  ¬_    : BExpr → BExpr

-- For now variables are evaluated to -9999
evalI : IExpr → ℤ
evalI (#   n)              = n
evalI (var _)              = -[1+ 9998 ]
evalI (a + b)              = evalI a +ℤ evalI b
evalI (a - b)              = evalI a -ℤ evalI b
evalI (a % b)              = evalI a modℤ evalI b
evalI (if b then a else c) = i (evalB b) t (evalI a) e (evalI c) 

--evalB : BExpr → Bool
evalB false    = false
evalB true     = true
evalB (x == y) = evalI x ==ℤ evalI y
evalB (x ≠ y)  = evalI x ≠ℤ evalI y
evalB (x < y)  = evalI x <ℤ evalI y
evalB (x ≤ y)  = evalI x ≤ℤ evalI y
evalB (x ∧ y)  = evalB x ∧b evalB y
evalB (x ∨ y)  = evalB x ∨b evalB y
evalB (¬ x)    = not (evalB x)

varNamesB : BExpr → List String

varNamesI : IExpr → List String
varNamesI (# x)                = []
varNamesI (var s)              = s ∷ []
varNamesI (x + y)              = varNamesI x ++ varNamesI y
varNamesI (x - y)              = varNamesI x ++ varNamesI y
varNamesI (x % y)              = varNamesI x ++ varNamesI y
varNamesI (if b then x else y) = varNamesB b ++ varNamesI x ++ varNamesI y

--varNamesB : BExpr → List String
varNamesB false     = []
varNamesB true      = []
varNamesB (x == y)  = varNamesI x ++ varNamesI y
varNamesB (x ≠ y)   = varNamesI x ++ varNamesI y
varNamesB (x < y)   = varNamesI x ++ varNamesI y
varNamesB (x ≤ y)   = varNamesI x ++ varNamesI y
varNamesB (x ∧ y)   = varNamesB x ++ varNamesB y
varNamesB (x ∨ y)   = varNamesB x ++ varNamesB y
varNamesB (¬ x)     = varNamesB x

-- Utility functions

N : ℕ → IExpr
N = #_ ∘ +_

_mod_ : IExpr → ℕ → IExpr
e mod n = e % N n

-- indicator function
χ : BExpr → IExpr
χ b = if b then N 1 else N 0
