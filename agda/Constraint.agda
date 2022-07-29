{-# OPTIONS --erased-cubical --safe #-}

module Constraint where

open import Prelude hiding (_∨_; _∧_; _==_; _-_; _mod_; #_)

open import Expr
open import Interval
open import Pitch

-- Pairs and pairs of pairs of IExpr
P PP : Type
P  = IExpr × IExpr
PP = P × P

data SetConstraint : Type where
  inSet : List ℤ → IExpr → SetConstraint

compileSetConstraint : SetConstraint → BExpr
compileSetConstraint (inSet ns i) = foldr (λ n x → (# n == i) ∨ x) false ns

-- Perfect union, fifth, octave only.
perInts perInts4 : List Opi
perInts  = map +_ (per1 ∷ per5 ∷ per8 ∷ [])
perInts4 = perInts ++ map +_ (per4 ∷ []) -- inclues 4th also

-- Assumes a ≤ b
perfectInterval perfectInterval4 : IExpr → IExpr → BExpr
perfectInterval a b  = compileSetConstraint (inSet perInts  ((b - a) mod 12))
perfectInterval4 a b = compileSetConstraint (inSet perInts4 ((b - a) mod 12))

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
  ¬ (perfectInterval4 c d ∧ compileMotionConstraint (similarOrParallel ((a , b) , c , d)))
  -- note that we currently handle 4ths

data Constraint : Type where
  setConstraint    : SetConstraint → Constraint
  motionConstraint : MotionConstraint → Constraint

compileConstraint : Constraint → BExpr
compileConstraint (setConstraint x)    = compileSetConstraint x
compileConstraint (motionConstraint x) = compileMotionConstraint x

inScaleConstraint : {n : ℕ} → Scale n → IExpr → Constraint
inScaleConstraint scale pitch =
  setConstraint (inSet (map (+_ ∘ toℕ) (toList scale)) (pitch mod 12))
