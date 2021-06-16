{-# OPTIONS --erased-cubical --safe #-}

module MakeTracks where

open import Data.Fin        using (Fin; #_; toℕ)
open import Data.List       using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; drop)
open import Data.Nat        using (_*_; ℕ; suc; _+_)
open import Data.Nat.Show   using (show)
open import Data.Product    using (_,_; uncurry)
open import Data.Vec        using (fromList; toList; Vec; _∷_; []; lookup) renaming (replicate to rep; zip to vzip; map to vmap; concat to vconcat; _++_ to _+v_)

open import Interval
open import Note
open import Pitch
open import MidiEvent
open import Util            using (fins')
open import Transformation

piano celesta vibraphone organ : InstrumentNumber-1
piano      = # 0
celesta    = # 8
vibraphone = # 11
organ      = # 17
drums      = # 0

-- sample assignment of instruments to tracks
-- Note that channel 10 (9 as Channel-1) is percussion
instruments : Vec InstrumentNumber-1 maxChannels
instruments =
  piano ∷ -- 1
  celesta ∷ -- 2
  vibraphone ∷ -- 3
  organ ∷ -- 4
  piano ∷ -- 5
  piano ∷ -- 6
  piano ∷ -- 7
  piano ∷ -- 8
  piano ∷ -- 9
  drums ∷ -- 10 (percussion)
  piano ∷ -- 11
  piano ∷ -- 12
  piano ∷ -- 13
  piano ∷ -- 14
  piano ∷ -- 15
  piano ∷ -- 16
  []

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
