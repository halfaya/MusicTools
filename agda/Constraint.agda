{-# OPTIONS --without-K --safe #-}

module Constraint where

open import Prelude hiding (_∨_; _∧_; _==_; _-_; _mod_; #_; _+_; ∣_∣; _≤_; if_then_else_)

open import Expr
open import Interval
open import Pitch
open import Util using (pairs)

-- NOTE: The convention is that the higher pitch is the first in any pair.

-- Convert a pair of pitches to an Opi
toOpi : (IExpr × IExpr) → IExpr
toOpi (p , q) = p - q

-- Convert a pair of pitches to an Opi mod 12
toOpi12 : (IExpr × IExpr) → IExpr
toOpi12 (p , q) = (p - q) mod 12

-- Convert a pair of pitches to a Upi
toUpi : (IExpr × IExpr) → IExpr
toUpi pq = ∣ toOpi pq ∣

data SetConstraint : Type where
  inSet : List ℤ → IExpr → SetConstraint

compileSetConstraint : SetConstraint → BExpr
compileSetConstraint (inSet ns i) = foldr (λ n x → (# n == i) ∨ x) false ns

-- Assumes a ≥ b
perfectInterval perfectInterval4 : IExpr → IExpr → BExpr
perfectInterval a b  = compileSetConstraint (inSet perInts  ((a - b) mod 12))
perfectInterval4 a b = compileSetConstraint (inSet perInts4 ((a - b) mod 12))

-- Given input (a,b),(c,d), assumes a ≥ b and c ≥ d
data MotionConstraint : Type where
  contrary             : PP → MotionConstraint
  oblique              : PP → MotionConstraint
  parallel             : PP → MotionConstraint
  similar              : PP → MotionConstraint
  direct               : PP → MotionConstraint -- similar or parallel
  notDirectIntoPerfect : PP → MotionConstraint

compileMotionConstraint : MotionConstraint → BExpr
compileMotionConstraint (contrary ((a , b) , c , d)) =
  (a < c ∧ b > d) ∨ (a > c ∧ b < d) 
compileMotionConstraint (oblique ((a , b) , c , d)) =
  (a == c ∧ b ≠ d) ∨ (a ≠ c ∧ b == d) 
compileMotionConstraint (parallel ((a , b) , c , d)) =
  c - a == d - b
compileMotionConstraint (similar ((a , b) , c , d)) =
  ((a < c ∧ b < d) ∨ (a > c ∧ b > d)) ∧ (c - a ≠ d - b)
compileMotionConstraint (direct ((a , b) , c , d)) =
  (a < c ∧ b < d) ∨ (a > c ∧ b > d) ∨ (a == c ∧ b == d)
compileMotionConstraint (notDirectIntoPerfect ((a , b) , c , d)) =
  ¬ (perfectInterval4 c d ∧ compileMotionConstraint (direct ((a , b) , c , d)))
  -- note that we currently include 4ths as perfect intervals

data NumericConstraint : Type where
  between      : IExpr → IExpr → IExpr → NumericConstraint -- a ≤ c ≤ b
  numContrary≥ :     ℤ → List PP       → NumericConstraint
  numLeaps≤    : ℤ → ℤ → List IExpr    → NumericConstraint -- first argument is max size of non-leap in semitones

compileNumericConstraint : NumericConstraint → BExpr
compileNumericConstraint (between a b c)     = a ≤ c ∧ c ≤ b
compileNumericConstraint (numContrary≥ n xs) =
  foldr (λ pp x → χ (compileMotionConstraint (contrary pp)) + x) (N 0) xs ≥ (# n)
compileNumericConstraint (numLeaps≤ max n ps) =
  let is = map toUpi (pairs ps)
  in foldr (λ upi x → χ (upi > # max) + x) (N 0) is ≤ (# n)

data BooleanConstraint : Type
data Constraint        : Type

data BooleanConstraint where
  andConstraint : Constraint → Constraint → BooleanConstraint
  orConstraint  : Constraint → Constraint → BooleanConstraint
  notConstraint : Constraint →              BooleanConstraint

compileConstraint : Constraint → BExpr

compileBooleanConstraint : BooleanConstraint → BExpr
compileBooleanConstraint (andConstraint a b) = compileConstraint a ∧ compileConstraint b
compileBooleanConstraint (orConstraint  a b) = compileConstraint a ∨ compileConstraint b
compileBooleanConstraint (notConstraint a)   = ¬ (compileConstraint a)

data Constraint where
  setConstraint     : SetConstraint → Constraint
  motionConstraint  : MotionConstraint → Constraint
  numericConstraint : NumericConstraint → Constraint
  booleanConstraint : BooleanConstraint → Constraint

-- compileConstraint : Constraint → BExpr
compileConstraint (setConstraint x)     = compileSetConstraint x
compileConstraint (motionConstraint x)  = compileMotionConstraint x
compileConstraint (numericConstraint x) = compileNumericConstraint x
compileConstraint (booleanConstraint x) = compileBooleanConstraint x

inScaleConstraint : {n : ℕ} → Scale n → IExpr → Constraint
inScaleConstraint scale pitch =
  setConstraint (inSet (map (+_ ∘ toℕ) (toList scale)) (pitch mod 12))

