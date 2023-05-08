{-# OPTIONS --without-K --safe #-}

module Expr where

open import Prelude hiding (#_; _==_; _+_; _mod_; ∣_∣; _≤_; lookup)
                    renaming ( _∨_ to _∨b_; _∧_ to _∧b_; _-_ to _-ℤ_; if_then_else_ to i_t_e_)

open import Util using (_==ℤ_; _≠ℤ_; _<ℤ_; _≤ℤ_; _>ℤ_; _≥ℤ_; _modℤ_)

infix 10 #_
infixr 9 ¬_
infixl 9 _%_ _mod_
infixl 8 _+_ _-_
infix  7 _==_ _≠_ _<_ _≤_ _>_ _≥_
infixr 6 _∧_
infixr 5 _∨_

Dict : Type
Dict = List (String × ℤ)

-- Returns 0 if not found.
lookup : Dict → String → ℤ
lookup []             s = + 0
lookup ((x , n) ∷ xs) s = i x ==s s t n e lookup xs s

lookupM : Dict → String → Maybe ℤ
lookupM []             s = nothing
lookupM ((x , n) ∷ xs) s = i x ==s s t (just n) e lookupM xs s

data BExpr : Type
evalB : Dict → BExpr → Bool

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
  _∧_   : BExpr → BExpr → BExpr
  _∨_   : BExpr → BExpr → BExpr
  ¬_    : BExpr → BExpr
  _==_  : IExpr → IExpr → BExpr
  _≠_   : IExpr → IExpr → BExpr
  _<_   : IExpr → IExpr → BExpr
  _≤_   : IExpr → IExpr → BExpr
  _>_   : IExpr → IExpr → BExpr
  _≥_   : IExpr → IExpr → BExpr

evalI : Dict → IExpr → ℤ
evalI _ (#   n)              = n
evalI d (var s)              = lookup d s
evalI d (a + b)              = evalI d a +ℤ evalI d b
evalI d (a - b)              = evalI d a -ℤ evalI d b
evalI d (a % b)              = evalI d a modℤ evalI d b
evalI d (if b then a else c) = i (evalB d b) t (evalI d a) e (evalI d c) 

--evalB : BExpr → Bool
evalB _ false    = false
evalB _ true     = true
evalB d (x ∧ y)  = evalB d x ∧b evalB d y
evalB d (x ∨ y)  = evalB d x ∨b evalB d y
evalB d (¬ x)    = not (evalB d x)
evalB d (x == y) = evalI d x ==ℤ evalI d y
evalB d (x ≠ y)  = evalI d x ≠ℤ evalI d y
evalB d (x < y)  = evalI d x <ℤ evalI d y
evalB d (x ≤ y)  = evalI d x ≤ℤ evalI d y
evalB d (x > y)  = evalI d x >ℤ evalI d y
evalB d (x ≥ y)  = evalI d x ≥ℤ evalI d y

{-
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
varNamesB (x ∧ y)   = varNamesB x ++ varNamesB y
varNamesB (x ∨ y)   = varNamesB x ++ varNamesB y
varNamesB (¬ x)     = varNamesB x
varNamesB (x == y)  = varNamesI x ++ varNamesI y
varNamesB (x ≠ y)   = varNamesI x ++ varNamesI y
varNamesB (x < y)   = varNamesI x ++ varNamesI y
varNamesB (x ≤ y)   = varNamesI x ++ varNamesI y
varNamesB (x > y)   = varNamesI x ++ varNamesI y
varNamesB (x ≥ y)   = varNamesI x ++ varNamesI y
-}

-- Utility functions

N : ℕ → IExpr
N = #_ ∘ +_

_mod_ : IExpr → ℕ → IExpr
e mod n = e % N n

∣_∣ : IExpr → IExpr
∣ n ∣ = if n ≥ N 0 then n else (N 0 - n)

-- indicator function
χ : BExpr → IExpr
χ b = if b then N 1 else N 0

-- Aggregates of IExpr
PP : Type
PP = (IExpr × IExpr) × (IExpr × IExpr)
{-
P PP [P] [[P]] : Type
P     = IExpr × IExpr
[P]   = List IExpr
[[P]] = List [P]
-}
