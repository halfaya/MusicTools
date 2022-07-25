{-# OPTIONS --erased-cubical --safe #-}

module Constraint where

open import Prelude hiding (_∨_; _∧_; _==_; #_; _-_)

open import Expr
open import Interval

-- Pair of pairs of IExpr
PP : Type
PP = (IExpr × IExpr) × (IExpr × IExpr)

data SetConstraint : Type where
  inSet : List ℤ → IExpr → SetConstraint

compileSetConstraint : SetConstraint → BExpr
compileSetConstraint (inSet ns i) = foldr (λ n x → (# n == i) ∨ x) false ns

-- Perfect union, fifth, octave and 12th only.
perInts : List Opi
perInts = map +_ (per1 ∷ per5 ∷ per8 ∷ per12 ∷ [])

-- Assumes a ≤ b
perfectInterval : IExpr → IExpr → BExpr
perfectInterval a b = compileSetConstraint (inSet perInts (b - a))

-- Given input (a,b),(c,d), assumes a ≤ b and c ≤ d
data MotionConstraint : Type where
  contrary              : PP → MotionConstraint
  oblique               : PP → MotionConstraint
  parallel              : PP → MotionConstraint
  similar               : PP → MotionConstraint
  similarOrParallel     : PP → MotionConstraint
  notSimilarIntoPerfect : PP → MotionConstraint

compileMotionConstraint : MotionConstraint → BExpr
compileMotionConstraint (contrary ((a , b) , c , d)) =
  (a < c ∧ d < b) ∨ (c < a ∧ b < d) 
compileMotionConstraint (oblique ((a , b) , c , d)) =
  (a == c ∧ b ≠ d) ∨ (a ≠ c ∧ b == d) 
compileMotionConstraint (parallel ((a , b) , c , d)) =
  c - a == d - b
compileMotionConstraint (similar ((a , b) , c , d)) =
  ((a < c ∧ b < d) ∨ (c < a ∧ d < b)) ∧ (c - a ≠ d - b)
compileMotionConstraint (similarOrParallel ((a , b) , c , d)) =
  (a < c ∧ b < d) ∨ (c < a ∧ d < b) ∨ (a == c ∧ b == d)
compileMotionConstraint (notSimilarIntoPerfect ((a , b) , c , d)) =
  ¬ (perfectInterval c d ∧ compileMotionConstraint (similarOrParallel ((a , b) , c , d)))

data Constraint : Type where
  setConstraint    : SetConstraint → Constraint
  motionConstraint : MotionConstraint → Constraint

compileConstraint : Constraint → BExpr
compileConstraint (setConstraint x)    = compileSetConstraint x
compileConstraint (motionConstraint x) = compileMotionConstraint x
