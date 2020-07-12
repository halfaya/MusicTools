{-# OPTIONS --without-K --safe #-}

module Canon where

open import Data.Fin     using (#_)
open import Data.Integer using (+_; -[1+_])
open import Data.List    using (List; _∷_; []; map; concat; _++_; replicate; zip; length; take; drop)
open import Data.Nat     using (_*_; ℕ; suc; _+_)
open import Data.Product using (_,_; uncurry)
open import Data.Vec     using (fromList; Vec; _∷_; []) renaming (replicate to rep; zip to vzip; map to vmap; concat to vconcat; _++_ to _+v_)
open import Function     using (_∘_)

open import Interval
open import Note
open import Pitch
open import MidiEvent

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

line1 line2 line3 line4 : List Note
line1 = subject ++ subject ++ subject
line2 = map (transposeNoteDown per5) (rest half  ∷ line1)
line3 = map (transposeNoteDown per8) (rest whole ∷ line1)
line4 = map (transposeNoteDown per8) (rest whole ∷ line2)

--------------

piano : InstrumentNumber-1
piano   = # 0

channel1 channel2 channel3 : Channel-1
channel1 = # 0
channel2 = # 1
channel3 = # 2
channel4 = # 3

tempo : ℕ
tempo = 120

velocity : Velocity
velocity = # 60

track1 track2 track3 : MidiTrack
track1 = track "Subject"  piano channel1 tempo (notes→events velocity line1)
track2 = track "Answer"   piano channel2 tempo (notes→events velocity line2)
track3 = track "Subject2" piano channel3 tempo (notes→events velocity line3)
track4 = track "Answer2"  piano channel4 tempo (notes→events velocity line4)

canonTracks : List MidiTrack
canonTracks = track1 ∷ track2 ∷ track3 ∷ track4 ∷ []
