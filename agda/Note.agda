{-# OPTIONS --without-K #-}

module Note where

open import Data.Integer using (ℤ)
open import Data.Nat     using (ℕ; _*_)

open import Pitch renaming (transpose to transposePitch)

data Duration : Set where
  duration : ℕ → Duration

data Note : Set where
  note : Duration → Pitch → Note
  rest : Duration         → Note

transpose : ℤ → Note → Note
transpose k (note d p) = note d (transposePitch k p)
transpose k (rest d)   = rest d

-- duration in 16th notes
16th 8th qtr half whole : ℕ → Duration
16th  n = duration n
8th   n = duration (2 * n)
qtr   n = duration (4 * n)
half  n = duration (8 * n)
whole n = duration (16 * n)
