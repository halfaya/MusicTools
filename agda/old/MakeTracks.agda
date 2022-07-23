{-# OPTIONS --erased-cubical --safe #-}

module MakeTracks where

open import Prelude

open import Data.Nat.Show   using (show)

open import Instruments
open import Interval
open import Note
open import Pitch
open import MidiEvent
open import Util            using (fins')
open import Transformation

velocity : Velocity
velocity = # 60

makeTrack : InstrumentNumber-1 → ℕ → Channel-1 → List Note → MidiTrack
makeTrack inst tempo n notes = track (show (suc (toℕ n))) inst n tempo (notes→events velocity notes)

makeTracks : {k : Fin maxChannels} → Vec InstrumentNumber-1 maxChannels → ℕ → Vec (List Note) (toℕ k) → Vec MidiTrack (toℕ k)
makeTracks {k} insts tempo lines =
  vmap (λ (i , ns) → makeTrack (lookup insts i) tempo i ns)
       (vzip (fins' maxChannels k) lines)

makeTrackList : {k : Fin maxChannels} → Vec InstrumentNumber-1 maxChannels → ℕ → Vec (List Note) (toℕ k) → List MidiTrack
makeTrackList {k} insts tempo lines = toList (makeTracks {k} insts tempo lines)
