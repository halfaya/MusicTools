{-# OPTIONS --without-K #-}

-- Counterpoint Exercises

module Exercises where

open import MidiEvent
open import Note
open import Pitch

open import Data.Fin
open import Data.List
open import Data.Nat

-- Exercise 5.4

cantusFirmus : List Pitch
cantusFirmus = a 4 ∷ c 5 ∷ b 4 ∷ c 5 ∷ d 5 ∷ e 5 ∷ c 5 ∷ b 4 ∷ a 4 ∷ []

cfNotes : List Note
cfNotes = Data.List.map (λ p → tone whole p) cantusFirmus

----

instrument : InstrumentNumber-1
instrument = # 0 -- piano

channel : Channel-1
channel = # 0

tempo : ℕ
tempo = 120

cfTrack : List MidiTrack
cfTrack = track "Piano" instrument channel tempo (notes→events defaultVelocity cfNotes) ∷ []

