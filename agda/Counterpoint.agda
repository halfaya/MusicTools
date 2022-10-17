{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude

open import Interval
open import Constraint hiding (motionConstraint; notDirectIntoPerfect)
open import Location
open import MConstraint
open import Symbolic
open import Util using (pairs; filter; middle; allPairsConcat)

------------------------------------------------

-- Allow up to two octaves.
firstSpeciesIntervals : List NInt
firstSpeciesIntervals = Min3 ∷ Maj3 ∷ Per5 ∷ Min6 ∷ Maj6 ∷ Per8 ∷ Min10 ∷ Maj10 ∷ Per12 ∷ Min13 ∷ Maj13 ∷ Per15 ∷ []

-- Allow perfect 4ths also.
firstSpeciesIntervals4 : List NInt
firstSpeciesIntervals4 = Per4 ∷ Per11 ∷ firstSpeciesIntervals

-- Expects lower voice first in each pair.
firstSpeciesConstraints : Key → List LP → List (Ranged MConstraint)
firstSpeciesConstraints k lp =
  let v1 = map snd lp
      v2 = map fst lp
  in map (mapRanged scaleConstraint ∘ locScaleConstraint k) (v1 ++ v2) ++
     map (mapRanged intervalConstraint ∘ locIntervalConstraint firstSpeciesIntervals) lp ++
     map (mapRanged motionConstraint ∘ locMotionConstraint notDirectIntoPerfect) (pairs lp)

allPairsConcatSwap : {A : Type} {n v : ℕ} → Vec (Vec A n) v → List (A × A)
allPairsConcatSwap xss = map swap (allPairsConcat (toList (vmap toList xss)))

firstSpeciesConstraintsAll : {n v : ℕ} → Key → Vec (Vec (Located NPitch) n) v → List (Ranged MConstraint)
firstSpeciesConstraintsAll k xss = firstSpeciesConstraints k (allPairsConcatSwap xss)

-- Constraints to make the music more interesting
interestingConstraints : List NP → List (Ranged MConstraint)
interestingConstraints ns =
  let ps = map np→p ns
      lp = index2VoiceBeat ns
      r  = fullRange2 ns
  in ranged r (constraint ((numericConstraint ∘ numContrary≥ (+ 6) ∘ pairs) ps)) ∷
     ranged r (constraint ((numericConstraint ∘ numLeaps≤ (+ per4) (+ 1) ∘ map snd) ps)) ∷
     ranged r (constraint ((numericConstraint ∘ numLeaps≤ (+ maj3) (+ 2) ∘ map snd) ps)) ∷ []
     --map (mapRanged intervalConstraint ∘ locIntervalConstraint firstSpeciesIntervals) (middle lp)

-- For synthesis, so don't need range
defaultConstraints : List NP → List MConstraint
defaultConstraints ns = map unrange (firstSpeciesConstraints (key C major) (index2VoiceBeat ns) ++ interestingConstraints ns)
