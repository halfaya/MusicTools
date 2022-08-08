{-# OPTIONS --erased-cubical --safe #-}

module Constraint where

open import Prelude hiding (_∨_; _∧_; _==_; _-_; _mod_; #_; _+_; ∣_∣)

open import Expr
open import Interval
open import Pitch
open import Util using (pairs)

-- Pairs and pairs of pairs of IExpr
P PP : Type
P  = IExpr × IExpr
PP = P × P

-- Convert a pair of pitches to an Opi
toOpi : P → IExpr
toOpi (p , q) = q - p

-- Convert a pair of pitches to a Upi
toUpi : P → IExpr
toUpi pq = ∣ toOpi pq ∣

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

data NumericConstraint : Type where
  numContrary≥ :     ℤ → List PP     → NumericConstraint
  numLeaps≤    : ℤ → ℤ → List IExpr  → NumericConstraint -- first argument is max size of non-leap in semitones

compileNumericConstraint : NumericConstraint → BExpr
compileNumericConstraint (numContrary≥ n xs) =
  foldr (λ pp x → χ (compileMotionConstraint (contrary pp)) + x) (N 0) xs ≥ (# n)
compileNumericConstraint (numLeaps≤ max n ps) =
  let is = map toUpi (pairs ps)
  in foldr (λ upi x → χ (upi > # max) + x) (N 0) is ≤ (# n)

data Constraint : Type where
  setConstraint     : SetConstraint → Constraint
  motionConstraint  : MotionConstraint → Constraint
  numericConstraint : NumericConstraint → Constraint

compileConstraint : Constraint → BExpr
compileConstraint (setConstraint x)     = compileSetConstraint x
compileConstraint (motionConstraint x)  = compileMotionConstraint x
compileConstraint (numericConstraint x) = compileNumericConstraint x

inScaleConstraint : {n : ℕ} → Scale n → IExpr → Constraint
inScaleConstraint scale pitch =
  setConstraint (inSet (map (+_ ∘ toℕ) (toList scale)) (pitch mod 12))
