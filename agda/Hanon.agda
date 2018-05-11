module Hanon where

open import Data.Fin     using (#_)
open import Data.Integer using (+_; -[1+_]; ℤ)
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; foldr)
open import Data.Nat     using (_*_; ℕ; suc; _+_)

open import Pitch
open import Note
open import Music        hiding (map) renaming (transpose to transposeMusic)
open import Midi
open import MidiEvent
open import Util

offsets : List ℤ
offsets = + 0 ∷ + 2 ∷ + 4 ∷ + 5 ∷ + 7 ∷ + 9 ∷ + 11 ∷ []

cell cell2 : Music
cell  = fromNotes (map (note (8th 1)) (c 2 ∷ e 2 ∷ f 2 ∷ g 2 ∷ a 2 ∷ g 2 ∷ f 2 ∷ e 2 ∷ []))
cell2 = cell ∥ transposeMusic -[1+ 11 ] cell

hanon1 : Music
hanon1 = foldr (λ t m → transposeMusic t cell2 ∷ m) nil offsets

----

instrument : InstrumentNumber-1
instrument = # 0 -- piano

channel : Channel-1
channel = # 0

tempo : ℕ
tempo = 180

hanonTrack : List MidiTrack
hanonTrack = track "Piano" instrument channel tempo (music→events defaultVelocity hanon1) ∷ []
