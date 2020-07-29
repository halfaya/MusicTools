{-# OPTIONS --without-K --safe #-}

module Note where

open import Data.Integer using (ℤ)
open import Data.Nat     using (ℕ; _+_; _*_)
open import Function     using (_∘_)

open import Pitch        using (Pitch; transposePitch)
open import Interval     using (Interval; SignedInterval; transposePitchInterval)

data Duration : Set where
  duration : ℕ → Duration

unduration : Duration → ℕ
unduration (duration d) = d

infixl 6 _d+_
_d+_ : Duration → Duration → Duration
duration a d+ duration b = duration (a + b)

data Note : Set where
  tone : Duration → Pitch → Note
  rest : Duration         → Note

-- Note: If we inline duration here Agda can't figure out
-- that noteDuration (tone d _) = unduration d
noteDuration : Note → ℕ
noteDuration (tone d _) = unduration d
noteDuration (rest d)   = unduration d

liftPitch : (Pitch → Pitch) → Note → Note
liftPitch f (tone d p) = tone d (f p)
liftPitch f (rest d)   = rest d

transposeNote : ℤ → Note → Note
transposeNote = liftPitch ∘ transposePitch

transposeNoteInterval : SignedInterval → Note → Note
transposeNoteInterval = liftPitch ∘ transposePitchInterval

-- duration in 16th notes
-- assume duration of a 16th note is 1
16th 8th d8th qtr dqtr half whole : Duration
16th   = duration 1
8th    = duration 2
d8th   = duration 3
qtr    = duration 4
dqtr   = duration 6
half   = duration 8
dhalf  = duration 12
whole  = duration 16
dwhole = duration 24
