{-# OPTIONS --erased-cubical --safe #-}

module MConstraint where

open import Prelude hiding (_-_; ∣_∣)

open import Constraint
open import Expr
open import Location
open import Symbolic

-- Higher-level musical constraints

-- Pairs and pairs of pairs of NPitch
NP NPNP LP LPLP : Type
NP   = NPitch × NPitch
NPNP = NP × NP
LP   = Located NPitch × Located NPitch
LPLP = LP × LP

np→p : NP → P
np→p (a , b) = name→pitch a , name→pitch b

npnp→pp : NPNP → PP
npnp→pp (a , b) = np→p a , np→p b

lp→np : LP → NP
lp→np (located _ a , located _ b) = a , b

lplp→npnp : LPLP → NPNP
lplp→npnp (a , b) = lp→np a , lp→np b

-- Assumes lower voice is first; range starts with higher voice
lpRange : LP → Range
lpRange (located l1 _ , located l2 _) = range l2 l1

-- Assumes lower voice is first; range starts with higher voice
lplpRange : LPLP → Range
lplpRange ((located l1 _ , located l2 _) , (located l3 _ , located l4 _)) = range l2 l3

-- Convert a pair of npitches to an NInt
-- If one or both is a variable, could result in a strange value.a
toNInt : NP → NInt
toNInt (p , q) with evalI (name→pitch p - name→pitch q)
... | +_     n = upi→name n
... | -[1+_] n = upi→name (suc n)

data Motion : Type where
  contrary              : Motion
  oblique               : Motion
  parallel              : Motion
  similar               : Motion
  similarOrParallel     : Motion
  notSimilarIntoPerfect : Motion

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

-- motion constraint indexed with range
locMotionConstraint : Motion → LPLP → Ranged MMotionConstraint
locMotionConstraint contrary              x = ranged (lplpRange x) (contrary              (lplp→npnp x))
locMotionConstraint oblique               x = ranged (lplpRange x) (oblique               (lplp→npnp x))
locMotionConstraint parallel              x = ranged (lplpRange x) (parallel              (lplp→npnp x))
locMotionConstraint similar               x = ranged (lplpRange x) (similar               (lplp→npnp x))
locMotionConstraint similarOrParallel     x = ranged (lplpRange x) (similarOrParallel     (lplp→npnp x))
locMotionConstraint notSimilarIntoPerfect x = ranged (lplpRange x) (notSimilarIntoPerfect (lplp→npnp x))

data MIntervalConstraint : Type where
  inSet : List NInt → NP → MIntervalConstraint

ic→sc : MIntervalConstraint → SetConstraint
ic→sc (inSet xs x) = inSet (map (+_ ∘ name→upi) xs) (toOpi (np→p x))

-- interval constraint indexed with range
locIntervalConstraint : List NInt → LP → Ranged MIntervalConstraint
locIntervalConstraint xs lp = ranged (lpRange lp) (inSet xs (lp→np lp))

data MScaleConstraint : Type where
  inScale : Key → NPitch → MScaleConstraint

msc→sc : MScaleConstraint → Constraint
msc→sc (inScale k x) = inScaleConstraint (toScale (scale k)) (name→pitch x)

-- interval constraint indexed with range
locScaleConstraint : Key → Located NPitch → Ranged MScaleConstraint
locScaleConstraint k (located loc x) = ranged (location loc) (inScale k x)

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

