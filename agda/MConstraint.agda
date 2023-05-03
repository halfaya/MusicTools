{-# OPTIONS --without-K --safe #-}

module MConstraint where

open import Prelude hiding (_-_; ∣_∣; #_)

open import Constraint
open import Expr
open import Location
open import Symbolic

-- Higher-level musical constraints

-- Convert a pair of mpitches to an NInt
toSInt : Dict → MP → SInt
toSInt d (p , q) with evalI d (name→iexpr p - name→iexpr q)
... | +_     n = upi→sint n
... | -[1+_] n = upi→sint (suc n)

data Motion : Type where
  contrary              : Motion
  oblique               : Motion
  parallel              : Motion
  similar               : Motion
  direct                : Motion
  notDirectIntoPerfect  : Motion

data MMotionConstraint : Type where
  contrary              : MPMP → MMotionConstraint
  oblique               : MPMP → MMotionConstraint
  parallel              : MPMP → MMotionConstraint
  similar               : MPMP → MMotionConstraint
  direct                : MPMP → MMotionConstraint
  notDirectIntoPerfect  : MPMP → MMotionConstraint

mmc→mc : MMotionConstraint → MotionConstraint
mmc→mc (contrary              x) = contrary              (mpmp→pp x)
mmc→mc (oblique               x) = oblique               (mpmp→pp x)
mmc→mc (parallel              x) = parallel              (mpmp→pp x)
mmc→mc (similar               x) = similar               (mpmp→pp x)
mmc→mc (direct                x) = direct                (mpmp→pp x)
mmc→mc (notDirectIntoPerfect  x) = notDirectIntoPerfect  (mpmp→pp x)

-- motion constraint indexed with range
locMotionConstraint : Motion → LPLP → Ranged MMotionConstraint
locMotionConstraint contrary              x = ranged (lplpRange x) (contrary              (lplp→mpmp x))
locMotionConstraint oblique               x = ranged (lplpRange x) (oblique               (lplp→mpmp x))
locMotionConstraint parallel              x = ranged (lplpRange x) (parallel              (lplp→mpmp x))
locMotionConstraint similar               x = ranged (lplpRange x) (similar               (lplp→mpmp x))
locMotionConstraint direct                x = ranged (lplpRange x) (direct                (lplp→mpmp x))
locMotionConstraint notDirectIntoPerfect  x = ranged (lplpRange x) (notDirectIntoPerfect  (lplp→mpmp x))

data MIntervalConstraint : Type where
  intervalType : List SInt → MP → MIntervalConstraint
  maxInterval  : SInt      → MP → MIntervalConstraint

ic→c : MIntervalConstraint → Constraint
ic→c (intervalType xs x) = setConstraint (inSet (map (+_ ∘ sint→upi) xs) (toOpi12 (mp→p x)))
ic→c (maxInterval m x) =
  numericConstraint (between (# (+ 1)) (# (+ (sint→upi m))) (toOpi (mp→p x)))

-- interval constraints indexed with range
locIntervalTypeConstraint : List SInt → LP → Ranged MIntervalConstraint
locIntervalTypeConstraint xs lp = ranged (lpRange lp) (intervalType xs (lp→mp lp))

locMaxIntervalConstraint : SInt → LP → Ranged MIntervalConstraint
locMaxIntervalConstraint m lp = ranged (lpRange lp) (maxInterval m (lp→mp lp))

data MScaleConstraint : Type where
  inScale : Key → MPitch → MScaleConstraint

msc→c : MScaleConstraint → Constraint
msc→c (inScale k x) = inScaleConstraint (toScale (scale k)) (name→iexpr x)

-- scale constraint indexed with range
locScaleConstraint : Key → Located MPitch → Ranged MScaleConstraint
locScaleConstraint k (located loc x) = ranged (point loc) (inScale k x)

{-
data MBooleanConstraint : Type where
  andConstraint : MConstraint → MConstraint → MBooleanConstraint
  orConstraint  : MConstraint → MConstraint → MBooleanConstraint
  notConstraint : MConstraint →               MBooleanConstraint


mbc→c : MBooleanConstraint → Constraint
mbc→c (andConstraint a b) = booleanConstraint (andConstraint (mc→c a) (mc→c b))
mbc→c (orConstraint  a b) = booleanConstraint (orConstraint  (mc→c a) (mc→c b))
mbc→c (notConstraint a)   = booleanConstraint (notConstraint (mc→c a))
-}

{-
data MMelodyConstraint : Type where
  passingTone : M3 → MMelodyConstraint

mmelc→c : MMelodyConstraint → Constraint
mmelc→c (passingTone (a , b , c)) =
  booleanConstraint (andConstraint (ic→c (intervalType steps (a , b)))
                                   (ic→c (intervalType steps (b , c))))
-}                                   

data MConstraint : Type where
  scaleConstraint    : MScaleConstraint    → MConstraint
  intervalConstraint : MIntervalConstraint → MConstraint
  motionConstraint   : MMotionConstraint   → MConstraint
--  booleanConstraint  : MBooleanConstraint  → MConstraint
--  melodyConstraint   : MMelodyConstraint   → MConstraint
  constraint         : Constraint          → MConstraint -- allows embedding arbitary lower-level constraints

mc→c : MConstraint → Constraint
mc→c (scaleConstraint    x) = msc→c x
mc→c (intervalConstraint x) = ic→c x
mc→c (motionConstraint   x) = motionConstraint (mmc→mc x)
--mc→c (booleanConstraint  x) = mbc→c x
--mc→c (melodyConstraint   x) = mmelc→c x
mc→c (constraint         x) = x


