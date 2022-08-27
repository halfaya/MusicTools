{-# OPTIONS --erased-cubical --safe #-}

module MConstraint where

open import Prelude hiding (_-_; ∣_∣)

open import Constraint
open import Expr
open import Symbolic

-- Higher-level musical constraints

-- Pairs and pairs of pairs of NPitch
NP NPNP : Type
NP   = NPitch × NPitch
NPNP = NP × NP

np→p : NP → P
np→p (a , b) = name→pitch a , name→pitch b

npnp→pp : NPNP → PP
npnp→pp (a , b) = np→p a , np→p b

-- Convert a pair of npitches to an NInt
-- If one or both is a variable, could result in a strange value.a
toNInt : NP → NInt
toNInt (p , q) with evalI (name→pitch p - name→pitch q)
... | +_     n = upi→name n
... | -[1+_] n = upi→name (suc n)

data MMotionConstraint : Type where
  contrary              : NPNP → MMotionConstraint
  oblique               : NPNP → MMotionConstraint
  parallel              : NPNP → MMotionConstraint
  similar               : NPNP → MMotionConstraint
  similarOrParallel     : NPNP → MMotionConstraint
  notSimilarIntoPerfect : NPNP → MMotionConstraint

mmc→mc : MMotionConstraint → MotionConstraint
mmc→mc (contrary              x) = contrary              (npnp→pp x)
mmc→mc (oblique               x) = oblique               (npnp→pp x)
mmc→mc (parallel              x) = parallel              (npnp→pp x)
mmc→mc (similar               x) = similar               (npnp→pp x)
mmc→mc (similarOrParallel     x) = similarOrParallel     (npnp→pp x)
mmc→mc (notSimilarIntoPerfect x) = notSimilarIntoPerfect (npnp→pp x)

data MIntervalConstraint : Type where
  inSet : List NInt → NInt → MIntervalConstraint

ic→sc : MIntervalConstraint → SetConstraint
ic→sc (inSet xs x) = inSet (map (+_ ∘ name→upi) xs) (N (name→upi x))

data MScaleConstraint : Type where
  inScale : Key → NPitch → MScaleConstraint

msc→sc : MScaleConstraint → Constraint
msc→sc (inScale k x) = inScaleConstraint (toScale (scale k)) (name→pitch x)

data MConstraint : Type where
  scaleConstraint    : MScaleConstraint    → MConstraint
  intervalConstraint : MIntervalConstraint → MConstraint
  motionConstraint   : MMotionConstraint   → MConstraint
  constraint         : Constraint          → MConstraint -- allows embedding arbitary lower-level constraints

mc→c : MConstraint → Constraint
mc→c (scaleConstraint    x) = msc→sc x
mc→c (intervalConstraint x) = setConstraint    (ic→sc x)
mc→c (motionConstraint   x) = motionConstraint (mmc→mc x)
mc→c (constraint         x) = x
