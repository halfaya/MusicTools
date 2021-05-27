{-# OPTIONS --cubical --safe #-}

module Canon where

open import Data.Fin        using (Fin; #_; toℕ)
open import Data.Integer    using (ℤ; +_; -[1+_]; _-_)
open import Data.List       using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; drop)
open import Data.Nat        using (_*_; ℕ; suc; _+_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Nat.Show   using (show)
open import Data.Product    using (_,_; uncurry)
open import Data.Sign       renaming (+ to s+ ; - to s-)
open import Data.Vec        using (fromList; toList; Vec; _∷_; []) renaming (replicate to rep; zip to vzip; map to vmap; concat to vconcat; _++_ to _+v_)
open import Function        using (_∘_)

open import Interval
open import Note
open import Pitch
open import MidiEvent
open import Util            using (repeat; fins')
open import Transformation

makeImitations : {k : ℕ} → List Note → Vec Opi k → Vec (List Note) k
makeImitations subject []       = []
makeImitations subject (i ∷ is) = map (transposeNoteInterval i) subject ∷ makeImitations subject is

addDelays : {k : ℕ} → Duration → Vec (List Note) k → Vec (List Note) k
addDelays (duration d) lines = ads 0 lines where
  ads : {k : ℕ} → ℕ → Vec (List Note) k → Vec (List Note) k
  ads n []              = []
  ads n (notes ∷ lines) = (rest (duration n) ∷ notes) ∷ ads (n + d) lines 

makeCanon : {k : ℕ} → List Note → ℕ → Duration → Vec Opi k → Vec (List Note) k
makeCanon subject reps d = addDelays d ∘ vmap (repeat reps) ∘ makeImitations subject

makeCanon2 : {k : ℕ} → List Note → Duration → Vec Opi k → Vec (List Note) k
makeCanon2 subject d is =
  addDelays d (makeImitations (
    repeat 2 subject ++
    inversion subject ++
    retrograde subject ++
    (retrograde ∘ inversion) subject)
    is)

--------------

piano : InstrumentNumber-1
piano   = # 0

velocity : Velocity
velocity = # 60

makeTrack : ℕ → Channel-1 → List Note → MidiTrack
makeTrack tempo n notes = track (show (suc (toℕ n))) piano n tempo (notes→events velocity notes)

-- Note that channel 10 (9 as Channel-1) is percussion, so best to stay under 10 channels.
makeTracks : {k : Fin maxChannels} → ℕ → Vec (List Note) (toℕ k) → Vec MidiTrack (toℕ k)
makeTracks {k} tempo lines = vmap (uncurry (makeTrack tempo)) (vzip (fins' maxChannels k) lines)

makeTrackList : {k : Fin maxChannels} → ℕ → Vec (List Note) (toℕ k) → List MidiTrack
makeTrackList tempo lines = toList (makeTracks tempo lines)
