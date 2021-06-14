{-# OPTIONS --erased-cubical --safe #-}

module FarmCanon where

open import Data.List       using (List; _∷_; [])
open import Data.Nat        using (ℕ)
open import Data.Sign       renaming (+ to s+ ; - to s-)
open import Data.Vec        using (Vec; _∷_; []; map)

open import Canon           using (makeCanon2; makeTrackList)
open import Interval
open import MidiEvent
open import Note
open import Pitch

subject : List Note
subject =
  tone qtr  (c 5) ∷
  tone qtr  (d 5) ∷
  tone half (e 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (e 5) ∷
  tone 8th  (d 5) ∷
  tone 8th  (d 5) ∷
  tone half (e 5) ∷
  []

transpositions : Vec Opi 4
transpositions = map (makeSigned s-) (per1 ∷ per5 ∷ per8 ∷ per12 ∷ [])

repeats : ℕ
repeats = 3

delay : Duration
delay = half

canon : Vec (List Note) 4
canon = makeCanon2 subject delay transpositions

tempo : ℕ
tempo = 120

canonTracks : List MidiTrack
canonTracks = makeTrackList tempo canon
