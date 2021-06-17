{-# OPTIONS --erased-cubical --safe #-}

module MakeTracks where

open import Data.Fin        using (Fin; #_; toℕ)
open import Data.List       using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; drop)
open import Data.Nat        using (_*_; ℕ; suc; _+_)
open import Data.Nat.Show   using (show)
open import Data.Product    using (_,_; uncurry)
open import Data.Vec        using (fromList; toList; Vec; _∷_; []; lookup) renaming (replicate to rep; zip to vzip; map to vmap; concat to vconcat; _++_ to _+v_)

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
makeTrackList insts tempo lines = toList (makeTracks insts tempo lines)
