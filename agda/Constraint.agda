{-# OPTIONS --erased-cubical --safe #-}

module Constraint where

open import Prelude hiding (_∨_; _==_; #_)

open import Expr

data SetConstraint : Type where
  inSet : List ℕ → ℕ → SetConstraint

compileSetConstraint : SetConstraint → BExpr
compileSetConstraint (inSet ns n) = foldr (λ m x → (# (+ m) == # (+ n)) ∨ x) false ns

-- Given input (a,b),(c,d), assumes a ≤ c and b ≤ d
data MotionConstraint : Type where
  similarIntoPerfect : (ℕ × ℕ) × (ℕ × ℕ) → MotionConstraint

