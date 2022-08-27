{-# OPTIONS --erased-cubical --safe #-}

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

ppNInt : NP → String
ppNInt (a , b) = showNPitch a ++s "," ++s showNPitch b ++s "(" ++s showNInt (nint a b) ++s ")"

ppPP : PP → String
ppPP ((a , b) , c , d) =
  ppInterval (evalI a) (evalI b) ++s " , " ++s ppInterval (evalI c) (evalI d)

ppNPNP : NPNP → String
ppNPNP (a , b) =
  ppNInt a ++s " , " ++s ppNInt b

ppMotionConstraint : MotionConstraint → String
ppMotionConstraint (contrary x)              = "Contrary "                        ++s ppPP x
ppMotionConstraint (oblique x)               = "Oblique "                         ++s ppPP x
ppMotionConstraint (parallel x)              = "Parallel "                        ++s ppPP x
ppMotionConstraint (similar x)               = "Similar "                         ++s ppPP x
ppMotionConstraint (similarOrParallel x)     = "SimilarOrParallel "               ++s ppPP x
ppMotionConstraint (notSimilarIntoPerfect x) = "NotParallelOrSimilarIntoPerfect " ++s ppPP x

ppMMotionConstraint : MMotionConstraint → String
ppMMotionConstraint (contrary x)              = "Contrary "                        ++s ppNPNP x
ppMMotionConstraint (oblique x)               = "Oblique "                         ++s ppNPNP x
ppMMotionConstraint (parallel x)              = "Parallel "                        ++s ppNPNP x
ppMMotionConstraint (similar x)               = "Similar "                         ++s ppNPNP x
ppMMotionConstraint (similarOrParallel x)     = "SimilarOrParallel "               ++s ppNPNP x
ppMMotionConstraint (notSimilarIntoPerfect x) = "NotParallelOrSimilarIntoPerfect " ++s ppNPNP x

ppMIntervalConstraint : MIntervalConstraint → String
ppMIntervalConstraint (inSet xs x) =
  "InIntervals " ++s ppList showNInt xs ++s " " ++s ppNInt x

ppMScaleConstraint : MScaleConstraint → String
ppMScaleConstraint (inScale k x) = "InScaleOfKey " ++s showKey k ++s " " ++s showNPitch x

ppConstraint : Constraint → String
ppConstraint (setConstraint x)     = "set constraint"
ppConstraint (motionConstraint x)  = "motion constraint"
ppConstraint (numericConstraint x) = "numeric constraint"

ppMConstraint : MConstraint → String
ppMConstraint (scaleConstraint    x) = ppMScaleConstraint x
ppMConstraint (intervalConstraint x) = ppMIntervalConstraint x
ppMConstraint (motionConstraint   x) = ppMMotionConstraint x
ppMConstraint (constraint         x) = ppConstraint x
