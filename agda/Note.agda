module Note where

open import Data.Integer using (ℤ)
open import Data.Nat     using (ℕ)

open import Pitch renaming (transpose to transposePitch)

data Duration : Set where
  duration : ℕ → Duration

data Note : Set where
  note : Duration → Pitch → Note
  rest : Duration         → Note

transpose : ℤ → Note → Note
transpose k (note d p) = note d (transposePitch k p)
transpose k (rest d)   = rest d
