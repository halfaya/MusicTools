{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude hiding (#_)

open import Constraint
open import Expr
open import Interval
open import Music
open import Note
open import Pitch
open import Interval
open import Util using (pairs; filter; _∘_)

------------------------------------------------

FirstSpecies2 : Type → Type
FirstSpecies2 A = List (A × A)

pairPairs : FirstSpecies2 Pitch → List PP
pairPairs [] = []
pairPairs (x ∷ []) = []
pairPairs ((a , b) ∷ (c , d) ∷ ps) =
  ((# (+ a), # (+ b)), (# (+ c), # (+ d))) ∷ pairPairs ((c , d) ∷ ps)

firstSpeciesIntervals : List Opi
firstSpeciesIntervals = map +_ (min3 ∷ maj3 ∷ per5 ∷ min6 ∷ maj6 ∷ per8 ∷ [])

unMaybe : {A : Type} → List (Maybe A × Maybe A) → List (A × A)
unMaybe [] = []
unMaybe ((just x , just y) ∷ []) = (x , y) ∷ []
unMaybe ((just x , just y) ∷ p ∷ xs) with unMaybe (p ∷ xs)
... | [] = []
... | (z ∷ zs) = (x , y) ∷ z ∷ zs
unMaybe ((nothing , just _)  ∷ _ ) = []
unMaybe ((just _  , nothing) ∷ _ ) = []
unMaybe ((nothing , nothing) ∷ _ ) = []

firstSpeciesConstraints : FirstSpecies2 Pitch → List Constraint
firstSpeciesConstraints ps =
  map (setConstraint ∘ inSet firstSpeciesIntervals ∘ #_ ∘ pitchPairToOpi) ps ++
  map (motionConstraint ∘ notSimilarIntoPerfect) (pairPairs ps)

