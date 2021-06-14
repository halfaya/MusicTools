{-# OPTIONS --erased-cubical --safe #-}

module Note where

open import Data.Integer using (ℤ)
open import Data.Nat     using (ℕ; _+_; _*_; ⌊_/2⌋)
open import Function     using (_∘_)

open import Pitch        using (Pitch; transposePitch)
open import Interval     using (Upi; Opi; transposePitchInterval)

Duration : Set
Duration = ℕ

data Note : Set where
  tone : Duration → Pitch → Note
  rest : Duration         → Note

noteDuration : Note → ℕ
noteDuration (tone d _) = d
noteDuration (rest d)   = d

liftPitch : (Pitch → Pitch) → Note → Note
liftPitch f (tone d p) = tone d (f p)
liftPitch f (rest d)   = rest d

transposeNote : ℤ → Note → Note
transposeNote = liftPitch ∘ transposePitch

transposeNoteInterval : Opi → Note → Note
transposeNoteInterval = liftPitch ∘ transposePitchInterval

-- rounds down
doubleSpeed : Note → Note
doubleSpeed (tone d p) = tone (⌊_/2⌋ d) p
doubleSpeed (rest d)   = rest (⌊_/2⌋ d)

slowDown : ℕ → Note → Note
slowDown k (tone d p) = tone (d * k) p
slowDown k (rest d)   = rest (d * k)

-- duration in 16th notes
-- assume duration of a 16th note is 1
16th 8th d8th qtr dqtr half whole : Duration
16th   = 1
8th    = 2
d8th   = 3
qtr    = 4
dqtr   = 6
half   = 8
dhalf  = 12
whole  = 16
dwhole = 24
