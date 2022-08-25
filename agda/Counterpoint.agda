{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude

open import HConstraint
open import Symbolic
open import Util using (pairs; filter; middle)

------------------------------------------------

-- Only allow up to an octave for now.
firstSpeciesIntervals : List NInt
firstSpeciesIntervals = Min3 ∷ Maj3 ∷ Per5 ∷ Min6 ∷ Maj6 ∷ Per8 ∷ []

-- Allow perfect 4ths also.
firstSpeciesIntervals4 : List NInt
firstSpeciesIntervals4 = Per4 ∷ firstSpeciesIntervals

firstSpeciesConstraints : List NP → List HConstraint
firstSpeciesConstraints ps = map (motionConstraint ∘ notSimilarIntoPerfect) (pairs ps)

{-
firstSpeciesConstraints : List P → List Constraint
firstSpeciesConstraints ps =
  let v1 = map snd ps
      v2 = map fst ps
  in map (inScaleConstraint majorScale) (v1 ++ v2) ++ -- for now assumes key is C
     map (setConstraint ∘ inSet firstSpeciesIntervals4 ∘ toOpi) ps ++
     map (motionConstraint ∘ notSimilarIntoPerfect) (pairs ps)

-- Contraints to make the music more interesting
interestingConstraints : List P → List Constraint
interestingConstraints ps =
  (numericConstraint ∘ numContrary≥ (+ 6) ∘ pairs) ps ∷
  (numericConstraint ∘ numLeaps≤ (+ maj3) (+ 1) ∘ map fst) ps ∷
  map (setConstraint ∘ inSet firstSpeciesIntervals ∘ toOpi) (middle ps)
-}
