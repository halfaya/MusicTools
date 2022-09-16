{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude

open import Interval
open import Constraint hiding (motionConstraint; notDirectIntoPerfect)
open import Location
open import MConstraint
open import Symbolic
open import Util using (pairs; filter; middle)

------------------------------------------------

-- Only allow up to an octave for now.
firstSpeciesIntervals : List NInt
firstSpeciesIntervals = Min3 ∷ Maj3 ∷ Per5 ∷ Min6 ∷ Maj6 ∷ Per8 ∷ []

-- Allow perfect 4ths also.
firstSpeciesIntervals4 : List NInt
firstSpeciesIntervals4 = Per4 ∷ firstSpeciesIntervals

firstSpeciesConstraints : Key → List NP → List (Ranged MConstraint)
firstSpeciesConstraints k ns =
  let lp = index2VoiceBeat ns
      v1 = map snd lp
      v2 = map fst lp
  in map (mapRanged scaleConstraint ∘ locScaleConstraint k) (v1 ++ v2) ++
     map (mapRanged intervalConstraint ∘ locIntervalConstraint firstSpeciesIntervals4) lp ++
     map (mapRanged motionConstraint ∘ locMotionConstraint notDirectIntoPerfect) (pairs lp)

-- Constraints to make the music more interesting
interestingConstraints : List NP → List (Ranged MConstraint)
interestingConstraints ns =
  let ps = map np→p ns
      lp = index2VoiceBeat ns
      r  = fullRange2 ns
  in ranged r (constraint ((numericConstraint ∘ numContrary≥ (+ 6) ∘ pairs) ps)) ∷
     ranged r (constraint ((numericConstraint ∘ numLeaps≤ (+ maj3) (+ 1) ∘ map fst) ps)) ∷
     map (mapRanged intervalConstraint ∘ locIntervalConstraint firstSpeciesIntervals) (middle lp)

-- For synthesis, so don't need range
defaultConstraints : List NP → List MConstraint
defaultConstraints ns = map unrange (firstSpeciesConstraints (key C major) ns ++ interestingConstraints ns)
