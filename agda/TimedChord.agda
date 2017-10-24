module TimedChord where

open import Data.Integer
open import Data.List
open import Data.Product renaming (map to pmap)
open import Function

open import Note
open import Chord

data Duration : Set where
  duration : ℤ → Duration

TimedChord = Chord × Duration

transposeTimedChord : ℤ → TimedChord → TimedChord
transposeTimedChord = (flip pmap) id ∘ transposeChord

transposeTimedChords : ℤ → List TimedChord → List TimedChord
transposeTimedChords = map ∘ transposeTimedChord
