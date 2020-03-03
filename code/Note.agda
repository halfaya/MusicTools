{-# OPTIONS --without-K #-}

module Note where

open import Data.Integer using (ℤ)
open import Data.Nat     using (ℕ; _*_)

open import Pitch        using (Pitch; transposePitch)

data Duration : Set where
  duration : ℕ → Duration

unduration : Duration → ℕ
unduration (duration d) = d

data Note : Set where
  tone : Duration → Pitch → Note
  rest : Duration         → Note

-- Note: If we inline duration here Agda can't figure out
-- that noteDuration (tone d _) = unduration d
noteDuration : Note → ℕ
noteDuration (tone d _) = unduration d
noteDuration (rest d)   = unduration d

transposeNote : ℤ → Note → Note
transposeNote k (tone d p) = tone d (transposePitch k p)
transposeNote k (rest d)   = rest d

-- duration in 16th notes
-- assume duration of a 16th note is 1
16th 8th qtr half whole : Duration
16th   = duration 1
8th    = duration 2
dqtr   = duration 3
qtr    = duration 4
half   = duration 8
dhalf  = duration 12
whole  = duration 16
dwhole = duration 24
