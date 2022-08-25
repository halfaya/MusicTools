{-# OPTIONS --erased-cubical --safe #-}

module PrettyPrint where

open import Prelude renaming (_-_ to _-ℤ_)

open import Constraint
open import HConstraint
open import Expr
open import Key
open import Pitch
open import Interval
open import Symbolic

ppNoteName : Key → ℤ → String
ppNoteName k (+_     n) =
  let (p , o) = absoluteToRelative n
  in showNoteName (lookup (keyNoteNames k) p) ++s primShowNat o
ppNoteName _ (-[1+_] n) = "Invalid note -" ++s primShowNat (suc n)

ppInterval : Key → ℤ → ℤ → String
ppInterval k x y with (y -ℤ x)
... | +_     n = ppNoteName k x ++s "," ++s ppNoteName k y ++s "(" ++s showInterval n ++s ")"
... | -[1+_] n = "Invalid interval -" ++s primShowNat (suc n)

ppNInt : NP → String
ppNInt (a , b) = showNPitch a ++s "," ++s showNPitch b ++s "(" ++s showNInt (nint a b) ++s ")"

ppPP : Key → PP → String
ppPP k ((a , b) , c , d) =
  ppInterval k (evalI a) (evalI b) ++s " , " ++s ppInterval k (evalI c) (evalI d)

ppNPNP : NPNP → String
ppNPNP (a , b) =
  ppNInt a ++s " , " ++s ppNInt b

ppMotionConstraint : Key → MotionConstraint → String
ppMotionConstraint k (contrary x)              = "Contrary "                        ++s ppPP k x
ppMotionConstraint k (oblique x)               = "Oblique "                         ++s ppPP k x
ppMotionConstraint k (parallel x)              = "Parallel "                        ++s ppPP k x
ppMotionConstraint k (similar x)               = "Similar "                         ++s ppPP k x
ppMotionConstraint k (similarOrParallel x)     = "SimilarOrParallel "               ++s ppPP k x
ppMotionConstraint k (notSimilarIntoPerfect x) = "NotParallelOrSimilarIntoPerfect " ++s ppPP k x

ppHMotionConstraint : HMotionConstraint → String
ppHMotionConstraint (contrary x)              = "Contrary "                        ++s ppNPNP x
ppHMotionConstraint (oblique x)               = "Oblique "                         ++s ppNPNP x
ppHMotionConstraint (parallel x)              = "Parallel "                        ++s ppNPNP x
ppHMotionConstraint (similar x)               = "Similar "                         ++s ppNPNP x
ppHMotionConstraint (similarOrParallel x)     = "SimilarOrParallel "               ++s ppNPNP x
ppHMotionConstraint (notSimilarIntoPerfect x) = "NotParallelOrSimilarIntoPerfect " ++s ppNPNP x

ppConstraint : Key → Constraint → String
ppConstraint k (setConstraint x)     = "set constraint"
ppConstraint k (motionConstraint x)  = ppMotionConstraint k x
ppConstraint k (numericConstraint x) = "numeric constraint"

ppHConstraint : HConstraint → String
ppHConstraint (motionConstraint x)  = ppHMotionConstraint x
