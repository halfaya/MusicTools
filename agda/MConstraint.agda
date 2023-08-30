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
  contrary              : MP2 → MMotionConstraint
  oblique               : MP2 → MMotionConstraint
  parallel              : MP2 → MMotionConstraint
  similar               : MP2 → MMotionConstraint
  direct                : MP2 → MMotionConstraint
  notDirectIntoPerfect  : MP2 → MMotionConstraint

mmc→mc : MMotionConstraint → MotionConstraint
mmc→mc (contrary              x) = contrary              (mp2→pp x)
mmc→mc (oblique               x) = oblique               (mp2→pp x)
mmc→mc (parallel              x) = parallel              (mp2→pp x)
mmc→mc (similar               x) = similar               (mp2→pp x)
mmc→mc (direct                x) = direct                (mp2→pp x)
mmc→mc (notDirectIntoPerfect  x) = notDirectIntoPerfect  (mp2→pp x)

-- motion constraint indexed with range
locMotionConstraint : Motion → LP2 → Ranged MMotionConstraint
locMotionConstraint contrary              x = ranged (lp2Range x) (contrary              (lp2→mp2 x))
locMotionConstraint oblique               x = ranged (lp2Range x) (oblique               (lp2→mp2 x))
locMotionConstraint parallel              x = ranged (lp2Range x) (parallel              (lp2→mp2 x))
locMotionConstraint similar               x = ranged (lp2Range x) (similar               (lp2→mp2 x))
locMotionConstraint direct                x = ranged (lp2Range x) (direct                (lp2→mp2 x))
locMotionConstraint notDirectIntoPerfect  x = ranged (lp2Range x) (notDirectIntoPerfect  (lp2→mp2 x))

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

data MMelodyConstraint : Type where
  passingTone : M3 → MMelodyConstraint

mmelc→c : MMelodyConstraint → Constraint
mmelc→c (passingTone (a , b , c)) =
  booleanConstraint (orConstraint
    (booleanConstraint (andConstraint (ic→c (intervalType steps (a , b)))
                                      (ic→c (intervalType steps (b , c)))))
    (booleanConstraint (andConstraint (ic→c (intervalType steps (c , b)))
                                      (ic→c (intervalType steps (b , a))))))

data MWeakBeatConstraint : Type where
  -- first argument is false if counterpoint is in first voice; true if in second voice
  consonantOrPassing : Bool → List SInt → MP3 → MWeakBeatConstraint

mwbc→c : MWeakBeatConstraint → Constraint
mwbc→c (consonantOrPassing false ints ((a , b) , (c , d) , e , f)) =
  booleanConstraint (orConstraint (ic→c (intervalType ints (c , d)))
                                  (mmelc→c (passingTone (a , c , e))))
mwbc→c (consonantOrPassing true  ints ((a , b) , (c , d) , e , f)) =
  booleanConstraint (orConstraint (ic→c (intervalType ints (c , d)))
                                  (mmelc→c (passingTone (b , d , f))))

data MConstraint : Type where
  scaleConstraint    : MScaleConstraint    → MConstraint
  intervalConstraint : MIntervalConstraint → MConstraint
  motionConstraint   : MMotionConstraint   → MConstraint
  melodyConstraint   : MMelodyConstraint   → MConstraint
  weakBeatConstraint : MWeakBeatConstraint → MConstraint
  constraint         : Constraint          → MConstraint -- allows embedding arbitary lower-level constraints

mc→c : MConstraint → Constraint
mc→c (scaleConstraint    x) = msc→c x
mc→c (intervalConstraint x) = ic→c x
mc→c (motionConstraint   x) = motionConstraint (mmc→mc x)
mc→c (melodyConstraint   x) = mmelc→c x
mc→c (weakBeatConstraint x) = mwbc→c x
mc→c (constraint         x) = x
