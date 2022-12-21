{-# OPTIONS --without-K --safe #-}

module PrettyPrint where

open import Prelude renaming (_-_ to _-ℤ_)

open import Constraint
open import MConstraint
open import Expr
open import Pitch
open import Interval
open import Symbolic

ppList : {A : Type} → (A → String) → List A → String
ppList f xs = "[" ++s ppl f xs ++s "]" where
  ppl : {A : Type} → (A → String) → List A → String
  ppl f []       = ""
  ppl f (x ∷ []) = f x
  ppl f (x ∷ y ∷ xs) = f x ++s "," ++s ppl f (y ∷ xs)

ppNoteName : ℤ → String
ppNoteName (+_     n) = showNPitch (pitch→npitch n)
ppNoteName (-[1+_] n) = "Invalid note -" ++s primShowNat (suc n)

ppInterval : ℤ → ℤ → String
ppInterval x y with (y -ℤ x)
... | +_     n = ppNoteName x ++s "," ++s ppNoteName y ++s "(" ++s showInterval n ++s ")"
... | -[1+_] n = "Invalid interval -" ++s primShowNat (suc n)

ppNInt : Dict → NP → String
ppNInt d (a , b) = showNPitch a ++s "," ++s showNPitch b ++s "(" ++s showNInt (nint d a b) ++s ")"

ppPP : Dict → PP → String
ppPP d ((a , b) , c , e) =
  ppInterval (evalI d a) (evalI d b) ++s " , " ++s ppInterval (evalI d c) (evalI d e)

ppNPNP : Dict → NPNP → String
ppNPNP d (a , b) =
  ppNInt d a ++s " , " ++s ppNInt d b

ppMotionConstraint : Dict → MotionConstraint → String
ppMotionConstraint d (contrary x)              = "Contrary "                        ++s ppPP d x  
ppMotionConstraint d (oblique x)               = "Oblique "                         ++s ppPP d x
ppMotionConstraint d (parallel x)              = "Parallel "                        ++s ppPP d x
ppMotionConstraint d (similar x)               = "Similar "                         ++s ppPP d x
ppMotionConstraint d (direct x)                = "Direct "                          ++s ppPP d x
ppMotionConstraint d (notDirectIntoPerfect x)  = "NotDirectIntoPerfect "            ++s ppPP d x

ppMMotionConstraint : Dict → MMotionConstraint → String
ppMMotionConstraint d (contrary x)              = "Contrary "                        ++s ppNPNP d x
ppMMotionConstraint d (oblique x)               = "Oblique "                         ++s ppNPNP d x
ppMMotionConstraint d (parallel x)              = "Parallel "                        ++s ppNPNP d x
ppMMotionConstraint d (similar x)               = "Similar "                         ++s ppNPNP d x
ppMMotionConstraint d (direct x)                = "Direct "                          ++s ppNPNP d x
ppMMotionConstraint d (notDirectIntoPerfect x)  = "NotDirectIntoPerfect "            ++s ppNPNP d x

ppMIntervalConstraint : Dict → MIntervalConstraint → String
ppMIntervalConstraint d (intervalType xs x) =
  "ItervalType " ++s ppList showNInt xs ++s " " ++s ppNInt d x
ppMIntervalConstraint d (maxInterval m x) =
  "IntervalBetween 1 ≤ " ++s ppNInt d x ++s " ≤ " ++s showNInt m

ppMScaleConstraint : MScaleConstraint → String
ppMScaleConstraint (inScale k x) = "InScaleOfKey " ++s showKey k ++s " " ++s showNPitch x

ppConstraint : Constraint → String
ppConstraint (setConstraint x)     = "set constraint"
ppConstraint (motionConstraint x)  = "motion constraint"
ppConstraint (numericConstraint x) = "numeric constraint"

ppMConstraint : Dict → MConstraint → String
ppMConstraint _ (scaleConstraint    x) = ppMScaleConstraint x
ppMConstraint d (intervalConstraint x) = ppMIntervalConstraint d x
ppMConstraint d (motionConstraint   x) = ppMMotionConstraint d x
ppMConstraint _ (constraint         x) = ppConstraint x
