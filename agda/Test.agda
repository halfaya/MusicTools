{-# OPTIONS --erased-cubical --safe #-}

module Test where

open import Prelude

open import Beethoven
open import Constraint
open import Counterpoint
open import Pitch
open import Interval

test : List (SetConstraint Upi × Upi)
test = checkFirstSpecies (unMaybe beethoven146a)


