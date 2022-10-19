{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude

open import Interval
open import Constraint hiding (motionConstraint; notDirectIntoPerfect)
open import Location
open import MConstraint
open import Symbolic
open import Util using (pairs; filter; middle; allPairs)

------------------------------------------------

-- Allow up to two octaves.
firstSpeciesIntervals : List NInt
firstSpeciesIntervals = Min3 ∷ Maj3 ∷ Per5 ∷ Min6 ∷ Maj6 ∷ Per8 ∷ Min10 ∷ Maj10 ∷ Per12 ∷ Min13 ∷ Maj13 ∷ Per15 ∷ []

-- Allow perfect 4ths also.
firstSpeciesIntervals4 : List NInt
firstSpeciesIntervals4 = Per4 ∷ Per11 ∷ firstSpeciesIntervals

firstSpeciesConstraintsVoice : Key → List (Located NPitch) → List (Ranged MConstraint)
firstSpeciesConstraintsVoice k v =
  map (mapRanged scaleConstraint ∘ locScaleConstraint k) v

-- Expects higher voice first in each pair.
firstSpeciesConstraints2 : List LP → List (Ranged MConstraint)
firstSpeciesConstraints2 lp =
     map (mapRanged intervalConstraint ∘ locIntervalConstraint firstSpeciesIntervals) lp ++
     map (mapRanged motionConstraint ∘ locMotionConstraint notDirectIntoPerfect) (pairs lp)

-- Returns a list of lists of all pairs of elements in each pair of lists.
-- Assumes all lists have the same length.
allPairsPairs : {ℓ : Level} {A : Type ℓ} → List (List A) → List (List (A × A))
allPairsPairs xss = map (uncurry zip) (allPairs xss)

firstSpeciesConstraints : Key → List (List (Located NPitch)) → List (Ranged MConstraint)
firstSpeciesConstraints k xss =
  let voiceConstraints = concat (map (firstSpeciesConstraintsVoice k) xss)
      pairConstraints  = concat (map firstSpeciesConstraints2 (allPairsPairs xss))
  in voiceConstraints ++ pairConstraints

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
--defaultConstraints : List NP → List MConstraint
--defaultConstraints ns = map unrange (firstSpeciesConstraints (key C major) (index2VoiceBeat ns) ++ interestingConstraints ns)
