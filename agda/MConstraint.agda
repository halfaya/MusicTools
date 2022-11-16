{-# OPTIONS --erased-cubical --safe #-}

module MConstraint where

open import Prelude hiding (_-_; ∣_∣; #_)

open import Constraint
open import Expr
open import Location
open import Symbolic

-- Higher-level musical constraints

-- Convert a pair of npitches to an NInt
toNInt : Dict → NP → NInt
toNInt d (p , q) with evalI d (name→pitch p - name→pitch q)
... | +_     n = upi→name n
... | -[1+_] n = upi→name (suc n)

data Motion : Type where
  contrary              : Motion
  oblique               : Motion
  parallel              : Motion
  similar               : Motion
  direct                : Motion
  notDirectIntoPerfect  : Motion

data MMotionConstraint : Type where
  contrary              : NPNP → MMotionConstraint
  oblique               : NPNP → MMotionConstraint
  parallel              : NPNP → MMotionConstraint
  similar               : NPNP → MMotionConstraint
  direct                : NPNP → MMotionConstraint
  notDirectIntoPerfect  : NPNP → MMotionConstraint

mmc→mc : MMotionConstraint → MotionConstraint
mmc→mc (contrary              x) = contrary              (npnp→pp x)
mmc→mc (oblique               x) = oblique               (npnp→pp x)
mmc→mc (parallel              x) = parallel              (npnp→pp x)
mmc→mc (similar               x) = similar               (npnp→pp x)
mmc→mc (direct                x) = direct                (npnp→pp x)
mmc→mc (notDirectIntoPerfect  x) = notDirectIntoPerfect  (npnp→pp x)

-- motion constraint indexed with range
locMotionConstraint : Motion → LPLP → Ranged MMotionConstraint
locMotionConstraint contrary              x = ranged (lplpRange x) (contrary              (lplp→npnp x))
locMotionConstraint oblique               x = ranged (lplpRange x) (oblique               (lplp→npnp x))
locMotionConstraint parallel              x = ranged (lplpRange x) (parallel              (lplp→npnp x))
locMotionConstraint similar               x = ranged (lplpRange x) (similar               (lplp→npnp x))
locMotionConstraint direct                x = ranged (lplpRange x) (direct                (lplp→npnp x))
locMotionConstraint notDirectIntoPerfect  x = ranged (lplpRange x) (notDirectIntoPerfect  (lplp→npnp x))

data MIntervalConstraint : Type where
  intervalType : List NInt → NP → MIntervalConstraint
  maxInterval  : NInt      → NP → MIntervalConstraint

ic→c : MIntervalConstraint → Constraint
ic→c (intervalType xs x) = setConstraint (inSet (map (+_ ∘ name→upi) xs) (toOpi12 (np→p x)))
ic→c (maxInterval m x) =
  numericConstraint (between (# (+ 1)) (# (+ (name→upi m))) (toOpi (np→p x)))

-- interval constraints indexed with range
locQualityConstraint : List NInt → LP → Ranged MIntervalConstraint
locQualityConstraint xs lp = ranged (lpRange lp) (intervalType xs (lp→np lp))

locMaxIntervalConstraint : NInt → LP → Ranged MIntervalConstraint
locMaxIntervalConstraint m lp = ranged (lpRange lp) (maxInterval m (lp→np lp))

data MScaleConstraint : Type where
  inScale : Key → NPitch → MScaleConstraint

msc→c : MScaleConstraint → Constraint
msc→c (inScale k x) = inScaleConstraint (toScale (scale k)) (name→pitch x)

-- interval constraint indexed with range
locScaleConstraint : Key → Located NPitch → Ranged MScaleConstraint
locScaleConstraint k (located loc x) = ranged (point loc) (inScale k x)

data MConstraint : Type where
  scaleConstraint    : MScaleConstraint    → MConstraint
  intervalConstraint : MIntervalConstraint → MConstraint
  motionConstraint   : MMotionConstraint   → MConstraint
  constraint         : Constraint          → MConstraint -- allows embedding arbitary lower-level constraints

mc→c : MConstraint → Constraint
mc→c (scaleConstraint    x) = msc→c x
mc→c (intervalConstraint x) = ic→c x
mc→c (motionConstraint   x) = motionConstraint (mmc→mc x)
mc→c (constraint         x) = x

