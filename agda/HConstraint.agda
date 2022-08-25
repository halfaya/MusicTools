{-# OPTIONS --erased-cubical --safe #-}

module HConstraint where

open import Prelude hiding (_∨_; _∧_; _==_; _-_; _mod_; #_; _+_; ∣_∣)

open import Constraint
open import Expr
open import Interval
open import Pitch
open import Symbolic

-- Pairs and pairs of pairs of NPitch
NP NPNP : Type
NP   = NPitch × NPitch
NPNP = NP × NP

np→p : NP → P
np→p (a , b) = name→pitch a , name→pitch b

npnp→pp : NPNP → PP
npnp→pp (a , b) = np→p a , np→p b

data HMotionConstraint : Type where
  contrary              : NPNP → HMotionConstraint
  oblique               : NPNP → HMotionConstraint
  parallel              : NPNP → HMotionConstraint
  similar               : NPNP → HMotionConstraint
  similarOrParallel     : NPNP → HMotionConstraint
  notSimilarIntoPerfect : NPNP → HMotionConstraint

hmc→mc : HMotionConstraint → MotionConstraint
hmc→mc (contrary              x) = contrary              (npnp→pp x)
hmc→mc (oblique               x) = oblique               (npnp→pp x)
hmc→mc (parallel              x) = parallel              (npnp→pp x)
hmc→mc (similar               x) = similar               (npnp→pp x)
hmc→mc (similarOrParallel     x) = similarOrParallel     (npnp→pp x)
hmc→mc (notSimilarIntoPerfect x) = notSimilarIntoPerfect (npnp→pp x)

data HConstraint : Type where
  motionConstraint : HMotionConstraint → HConstraint

hc→c : HConstraint → Constraint
hc→c (motionConstraint x) = motionConstraint (hmc→mc x)
