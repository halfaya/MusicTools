{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude hiding (#_; _-_)

open import Constraint
open import Expr
open import Interval
open import Music
open import Note
open import Pitch
open import Interval
open import Util using (pairs; filter)

------------------------------------------------

pairPairs : List P → List PP
pairPairs [] = []
pairPairs (x ∷ []) = []
pairPairs (a ∷ b ∷ ps) = (a , b) ∷ pairPairs (b ∷ ps)

-- Only allow up to an octave for now.
firstSpeciesIntervals : List Opi
firstSpeciesIntervals = map +_ (min3 ∷ maj3 ∷ per5 ∷ min6 ∷ maj6 ∷ per8 ∷ {- min10 ∷ maj10 ∷ per12 ∷ -} [])

-- Allow perfect 4ths also.
firstSpeciesIntervals4 : List Opi
firstSpeciesIntervals4 = map +_ (per4 ∷ {- per11 ∷ -} []) ++ firstSpeciesIntervals

toOpi : P → IExpr
toOpi (a , b) = b - a

firstSpeciesConstraints : List P → List Constraint
firstSpeciesConstraints ps =
  let v1 = map snd ps
      v2 = map fst ps
  in map (inScaleConstraint majorScale) (v1 ++ v2) ++ -- for now assumes key is C
     map (setConstraint ∘ inSet firstSpeciesIntervals4 ∘ toOpi) ps ++
     map (motionConstraint ∘ notSimilarIntoPerfect) (pairPairs ps)

-- Contraints to make the music more interesting
interestingConstraints : List P → List Constraint
interestingConstraints ps = (numericConstraint ∘ numContrary≥ (+ 6) ∘ pairPairs) ps ∷ []
