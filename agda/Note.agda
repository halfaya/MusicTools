{-# OPTIONS --without-K #-}

module Note where

open import Data.Integer using (ℤ)
open import Data.Nat     using (ℕ; _*_)

open import Pitch renaming (transpose to transposePitch)

data Duration : Set where
  duration : ℕ → Duration

data Note : Set where
  tone : Duration → Pitch → Note
  rest : Duration         → Note

transpose : ℤ → Note → Note
transpose k (tone d p) = tone d (transposePitch k p)
transpose k (rest d)   = rest d

-- duration in 16th notes
-- assume duration of a 16th note is 1
16th 8th qtr half whole : Duration
16th  = duration 1
8th   = duration 2
qtr   = duration 4
half  = duration 8
whole = duration 16
