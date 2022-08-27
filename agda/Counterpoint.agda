{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude

open import Interval
open import Constraint hiding (motionConstraint; notSimilarIntoPerfect)
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

firstSpeciesConstraints : Key → List NP → List MConstraint
firstSpeciesConstraints k ns =
  let v1 = map snd ns
      v2 = map fst ns
  in map (scaleConstraint ∘ inScale k ) (v1 ++ v2) ++
     map (intervalConstraint ∘ inSet firstSpeciesIntervals4) ns ++
     map (motionConstraint ∘ notSimilarIntoPerfect) (pairs ns)

-- Constraints to make the music more interesting
interestingConstraints : List NP → List MConstraint
interestingConstraints ns =
  let ps = map np→p ns
  in constraint ((numericConstraint ∘ numContrary≥ (+ 6) ∘ pairs) ps) ∷
     constraint ((numericConstraint ∘ numLeaps≤ (+ maj3) (+ 1) ∘ map fst) ps) ∷
     map (intervalConstraint ∘ inSet firstSpeciesIntervals) (middle ns)

defaultConstraints : List NP → List MConstraint
defaultConstraints ns = firstSpeciesConstraints (key C major) ns ++ interestingConstraints ns
