{-# OPTIONS --without-K --safe #-}

module Canon where

open import Data.Fin        using (Fin; #_; toℕ)
open import Data.Integer    using (+_; -[1+_])
open import Data.List       using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; drop)
open import Data.Nat        using (_*_; ℕ; suc; _+_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Nat.Show   using (show)
open import Data.Product    using (_,_; uncurry)
open import Data.Sign       renaming (+ to s+ ; - to s-)
open import Data.Vec        using (fromList; Vec; _∷_; []) renaming (replicate to rep; zip to vzip; map to vmap; concat to vconcat; _++_ to _+v_)
open import Function        using (_∘_)

open import Interval
open import Note
open import Pitch
open import MidiEvent
open import Util            using (repeat)

makeImitations : List Note → List SignedInterval → List (List Note)
makeImitations subject []       = []
makeImitations subject (i ∷ is) = map (transposeNoteInterval i) subject ∷ makeImitations subject is

addDelays : Duration → List (List Note) → List (List Note)
addDelays (duration d) lines = ads 0 lines where
  ads : ℕ → List (List Note) → List (List Note)
  ads n []              = []
  ads n (notes ∷ lines) = (rest (duration n) ∷ notes) ∷ ads (n + d) lines 

makeCanon : List Note → ℕ → Duration → List SignedInterval → List (List Note)
makeCanon subject n d = addDelays d ∘ map (repeat n) ∘ (subject ∷_) ∘ makeImitations subject

--------------

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

transpositions : List SignedInterval
transpositions = map (makeSigned s-) (per5 ∷ per8 ∷ per12 ∷ [])

canon : List (List Note)
canon = makeCanon subject 3 half transpositions

--------------

piano : InstrumentNumber-1
piano   = # 0

tempo : ℕ
tempo = 120

velocity : Velocity
velocity = # 60

makeTrack : Fin 16 → List Note → MidiTrack
makeTrack n notes = track (show (suc (toℕ n))) piano n tempo (notes→events velocity notes)

-- Combines tracks onto channels if more than 16 tracks.
makeTracks : List (List Note) → List MidiTrack
makeTracks lines = mt 0 lines where
  mt : ℕ → List (List Note) → List MidiTrack
  mt index [] = []
  mt index (notes ∷ lines) = makeTrack (index mod 16) notes ∷ mt (suc index) lines

canonTracks : List MidiTrack
canonTracks = makeTracks canon
