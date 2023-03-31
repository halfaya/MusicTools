{-# OPTIONS --without-K --safe #-}

module PrettyPrint where

open import Prelude renaming (_-_ to _-ℤ_)

open import Constraint
open import MConstraint
open import Expr
open import Pitch
open import Interval
open import Symbolic

ppParen : String → String
ppParen s = "(" ++s s ++s ")"

ppList : {A : Type} → (A → String) → List A → String
ppList f xs = "[" ++s ppl f xs ++s "]" where
  ppl : {A : Type} → (A → String) → List A → String
  ppl f []       = ""
  ppl f (x ∷ []) = f x
  ppl f (x ∷ y ∷ xs) = f x ++s "," ++s ppl f (y ∷ xs)

ppNoteName : ℤ → String
ppNoteName (+_     n) = showSPitch (pitch→np n)
ppNoteName (-[1+_] n) = "Invalid note -" ++s showℕ (suc n)

ppInterval : ℤ → ℤ → String
ppInterval x y with (y -ℤ x)
... | +_     n = ppNoteName x ++s "," ++s ppNoteName y ++s "(" ++s showInterval n ++s ")"
... | -[1+_] n = "Invalid interval -" ++s showℕ (suc n)

ppSInt : Dict → MP → String
ppSInt d (a , b) = showMPitch a ++s "," ++s showMPitch b ++s "(" ++s showSInt (sint d a b) ++s ")"

ppPP : Dict → PP → String
ppPP d ((a , b) , c , e) =
  ppInterval (evalI d a) (evalI d b) ++s " , " ++s ppInterval (evalI d c) (evalI d e)

ppMPMP : Dict → MPMP → String
ppMPMP d (a , b) =
  ppSInt d a ++s " , " ++s ppSInt d b

ppMotionConstraint : Dict → MotionConstraint → String
ppMotionConstraint d (contrary x)              = "Contrary "                        ++s ppPP d x  
ppMotionConstraint d (oblique x)               = "Oblique "                         ++s ppPP d x
ppMotionConstraint d (parallel x)              = "Parallel "                        ++s ppPP d x
ppMotionConstraint d (similar x)               = "Similar "                         ++s ppPP d x
ppMotionConstraint d (direct x)                = "Direct "                          ++s ppPP d x
ppMotionConstraint d (notDirectIntoPerfect x)  = "NotDirectIntoPerfect "            ++s ppPP d x

ppMMotionConstraint : Dict → MMotionConstraint → String
ppMMotionConstraint d (contrary x)              = "Contrary "                        ++s ppMPMP d x
ppMMotionConstraint d (oblique x)               = "Oblique "                         ++s ppMPMP d x
ppMMotionConstraint d (parallel x)              = "Parallel "                        ++s ppMPMP d x
ppMMotionConstraint d (similar x)               = "Similar "                         ++s ppMPMP d x
ppMMotionConstraint d (direct x)                = "Direct "                          ++s ppMPMP d x
ppMMotionConstraint d (notDirectIntoPerfect x)  = "NotDirectIntoPerfect "            ++s ppMPMP d x

ppMIntervalConstraint : Dict → MIntervalConstraint → String
ppMIntervalConstraint d (intervalType xs x) =
  "IntervalType " ++s ppList showSInt xs ++s " " ++s ppSInt d x
ppMIntervalConstraint d (maxInterval m x) =
  "IntervalBetween 1 ≤ " ++s ppSInt d x ++s " ≤ " ++s showSInt m

ppMScaleConstraint : MScaleConstraint → String
ppMScaleConstraint (inScale k x) = "InScaleOfKey " ++s showKey k ++s " " ++s showMPitch x

ppMConstraint : Dict → MConstraint → String

{-
ppMBooleanConstraint : Dict → MBooleanConstraint → String
ppMBooleanConstraint d (andConstraint a b) = ppParen (ppMConstraint d a) ++s " and " ++s ppParen (ppMConstraint d b)
ppMBooleanConstraint d (orConstraint  a b) = ppParen (ppMConstraint d a) ++s " or "  ++s ppParen (ppMConstraint d b)
ppMBooleanConstraint d (notConstraint a)   = "not " ++s ppParen (ppMConstraint d a)
-}

ppMMelodyConstraint : Dict → MMelodyConstraint → String
ppMMelodyConstraint d (passingTone (a , b , c)) = "passing tone " ++s (ppSInt d (a , b)) ++s " " ++s (ppSInt d (b , c))

ppConstraint : Constraint → String
ppConstraint (setConstraint x)     = "set constraint"
ppConstraint (motionConstraint x)  = "motion constraint"
ppConstraint (numericConstraint x) = "numeric constraint"
ppConstraint (booleanConstraint x) = "boolean constraint"

-- ppMConstraint : Dict → MConstraint → String
ppMConstraint _ (scaleConstraint    x) = ppMScaleConstraint x
ppMConstraint d (intervalConstraint x) = ppMIntervalConstraint d x
ppMConstraint d (motionConstraint   x) = ppMMotionConstraint d x
--ppMConstraint d (booleanConstraint  x) = ppMBooleanConstraint d x
ppMConstraint d (melodyConstraint  x)  = ppMMelodyConstraint d x
ppMConstraint _ (constraint         x) = ppConstraint x

