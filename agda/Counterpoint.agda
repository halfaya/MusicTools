{-# OPTIONS --erased-cubical --safe #-}

-- First and second species counterpoint
module Counterpoint where

open import Prelude

open import Constraint
open import Interval
open import Music
open import Note
open import Pitch
open import Interval
open import Util using (pairs; filter; _∘_)

------------------------------------------------

FirstSpecies2 : Type → Type
FirstSpecies2 A = List (A × A)

firstSpeciesIntervals : List Upi
firstSpeciesIntervals = min3 ∷ maj3 ∷ per5 ∷ min6 ∷ maj6 ∷ per8 ∷ []

unMaybe : {A : Type} → List (Maybe A × Maybe A) → List (A × A)
unMaybe [] = []
unMaybe ((just x , just y) ∷ []) = (x , y) ∷ []
unMaybe ((just x , just y) ∷ p ∷ xs) with unMaybe (p ∷ xs)
... | [] = []
... | (z ∷ zs) = (x , y) ∷ z ∷ zs
unMaybe ((nothing , just _)  ∷ _ ) = []
unMaybe ((just _  , nothing) ∷ _ ) = []
unMaybe ((nothing , nothing) ∷ _ ) = []

checkFirstSpecies : FirstSpecies2 Pitch → List (SetConstraint Upi × Upi)
checkFirstSpecies xs =
  filter
    (not ∘ uncurry (checkSetConstraint (_==_)))
    (map (λ x → inSet firstSpeciesIntervals , (absoluteInterval ∘ pitchPairToOpi) x) xs)

